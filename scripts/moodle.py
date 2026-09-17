#!/usr/bin/env python3
"""Read Moodle through its mobile Web Services. Python 3.10+, no core dependencies."""
from __future__ import annotations

import argparse
import datetime as dt
import getpass
import html
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import ssl
import sys
import tempfile
import time
import urllib.error
import urllib.parse as url
import urllib.request
import warnings
from zoneinfo import ZoneInfo, ZoneInfoNotFoundError

DEFAULT_SITE = "https://edu.mmcs.sfedu.ru"
DEFAULT_CONFIG = Path.home() / ".config" / "moodle-mmcs" / "config.json"
UTC = dt.timezone.utc
SECRETS: set[str] = set()
SECRET_KEYS = {"token", "wstoken", "authtoken", "privatetoken", "sesskey", "password", "cookie", "authorization"}
MODULES = {
    "quiz": "quizzes", "page": "pages", "url": "urls", "resource": "resources",
    "folder": "folders", "book": "books", "forum": "forums", "lesson": "lessons",
    "choice": "choices", "feedback": "feedbacks", "workshop": "workshops",
    "scorm": "scorms", "h5pactivity": "h5pactivities", "glossary": "glossaries",
    "wiki": "wikis", "data": "databases", "survey": "surveys", "imscp": "imscps", "lti": "ltis",
}
DEADLINES = {"assign": "duedate", "quiz": "timeclose", "lesson": "deadline",
             "choice": "timeclose", "feedback": "timeclose", "workshop": "submissionend",
             "data": "timeavailableto", "scorm": "timeclose"}
READ_FUNCTIONS = {
    "core_webservice_get_site_info", "core_enrol_get_users_courses", "core_course_get_contents",
    "core_course_get_course_module", "core_calendar_get_calendar_events",
    "core_calendar_get_calendar_event_by_id", "mod_assign_get_assignments",
    "mod_assign_get_submission_status", "mod_forum_get_forum_discussions",
    "mod_forum_get_discussion_posts", "mod_glossary_get_entries_by_letter",
    "mod_wiki_get_subwikis", "mod_wiki_get_subwiki_pages", "mod_wiki_get_page_contents",
    "mod_data_get_entries",
} | {f"mod_{kind}_get_{plural}_by_courses" for kind, plural in MODULES.items()}
HTML_FIELDS = {"intro", "activity", "content", "cachedcontent", "description", "summary", "message", "definition",
               "availabilityinfo", "gradefordisplay", "submissionstatement"}


class MoodleError(Exception):
    def __init__(self, code, message):
        super().__init__(message)
        self.code = str(code)


def clean(value):
    """Redact recursively, including credentials embedded in HTML links and error text."""
    if isinstance(value, dict):
        return {k: ("[REDACTED]" if k.lower() in SECRET_KEYS else clean(v)) for k, v in value.items()}
    if isinstance(value, list):
        return [clean(v) for v in value]
    if isinstance(value, str):
        for secret in sorted(SECRETS, key=len, reverse=True):
            if secret:
                value = value.replace(secret, "[REDACTED]").replace(url.quote(secret, safe=""), "[REDACTED]")
        value = re.sub(r"(?i)((?:[?&]|&amp;)(?:token|wstoken|authtoken|privatetoken|sesskey|password)=)[^\s&#\"'<>]+", r"\1[REDACTED]", value)
    return value


def site_url(value):
    p = url.urlsplit(value.strip())
    if p.scheme != "https" or not p.hostname or p.username or p.password or p.query or p.fragment:
        raise MoodleError("invalid_site", "Укажите HTTPS-адрес Moodle без параметров, логина и пароля.")
    return value.strip().rstrip("/")


def same_site(site, target):
    a, b = url.urlsplit(site), url.urlsplit(target)
    return (a.scheme, a.hostname, a.port) == (b.scheme, b.hostname, b.port) and (
        b.path == a.path or b.path.startswith(a.path.rstrip("/") + "/")) and not b.username and not b.password


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise MoodleError("redirect", "Сервер перенаправил запрос. Проверьте канонический адрес Moodle; секрет не переслан.")


class Transport:
    def __init__(self, timeout=30):
        self.timeout = timeout
        self.opener = urllib.request.build_opener(NoRedirect(), urllib.request.HTTPSHandler(context=ssl.create_default_context()))

    def fetch(self, target, data=None, content_type=None, limit=32 * 1024 * 1024, retry=True):
        req = urllib.request.Request(target, data=data, headers={"User-Agent": "moodle-mmcs/1.0"})
        if content_type:
            req.add_header("Content-Type", content_type)
        for attempt in range(3 if retry else 1):
            try:
                with self.opener.open(req, timeout=self.timeout) as response:
                    body = response.read(limit + 1)
                    if len(body) > limit:
                        raise MoodleError("response_too_large", "Ответ превышает лимит размера; данные не усечены молча.")
                    return body, response.headers.get("Content-Type", "")
            except urllib.error.HTTPError as exc:
                if retry and exc.code in (429, 502, 503, 504) and attempt < 2:
                    time.sleep(attempt + 1)
                    continue
                raise MoodleError("http_error", f"Moodle вернул HTTP {exc.code}.") from None
            except (urllib.error.URLError, TimeoutError, OSError):
                if retry and attempt < 2:
                    time.sleep(attempt + 1)
                    continue
                raise MoodleError("network_error", "Не удалось подключиться к Moodle: проверьте сеть, HTTPS-сертификат и адрес.") from None

    def json(self, target, params=None, payload=None, retry=True):
        if payload is not None:
            body = json.dumps(payload).encode()
            mime = "application/json"
        else:
            body = url.urlencode(flatten(params or {})).encode()
            mime = "application/x-www-form-urlencoded"
        raw, _ = self.fetch(target, body, mime, retry=retry)
        try:
            result = json.loads(raw)
        except (ValueError, UnicodeError):
            raise MoodleError("not_json", "Moodle вернул HTML или некорректный JSON. Возможны SSO, техработы или неверный адрес.") from None
        if isinstance(result, dict) and (result.get("exception") or result.get("errorcode") or result.get("error")):
            code = result.get("errorcode", "moodle_error")
            messages = {
                "invalidlogin": "Логин или пароль не принят. Повторного входа автоматически не будет.",
                "invalidtoken": "Токен недействителен или истёк. Повторите setup.",
                "accessexception": "Сервис не разрешает этот запрос. Проверьте doctor или повторите setup.",
                "servicenotavailable": "Мобильный сервис Moodle недоступен этому аккаунту.",
                "enablewsdescription": "Web Services отключены на сервере Moodle.",
                "requirecorrectaccess": "Сервер требует другой способ входа; используйте существующий API-токен.",
            }
            raise MoodleError(code, messages.get(code, "Moodle отклонил запрос. Код ошибки: " + re.sub(r"[^\w.-]", "", str(code))))
        return result


def flatten(value, prefix=""):
    result = []
    if isinstance(value, dict):
        for key, item in value.items():
            result.extend(flatten(item, f"{prefix}[{key}]" if prefix else key))
    elif isinstance(value, (list, tuple)):
        for i, item in enumerate(value):
            result.extend(flatten(item, f"{prefix}[{i}]"))
    elif value is not None:
        result.append((prefix, int(value) if isinstance(value, bool) else value))
    return result


def private_write(path, data, overwrite=True):
    path = Path(path).expanduser()
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
    if not overwrite and path.exists():
        raise MoodleError("file_exists", "Файл назначения уже существует. Выберите другое имя.")
    fd, temp = tempfile.mkstemp(prefix=".moodle-", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
        if overwrite:
            os.replace(temp, path)
        else:
            os.link(temp, path)  # Atomic no-clobber, even if another writer races us.
            os.unlink(temp)
    finally:
        if os.path.exists(temp):
            os.unlink(temp)


def secret_prompt(prompt, strip=True):
    if not sys.stdin.isatty():
        raise MoodleError("interactive_setup", "Запустите setup самостоятельно в обычном терминале: секрет вводится скрыто.")
    with warnings.catch_warnings():
        warnings.simplefilter("error", getpass.GetPassWarning)
        try:
            value = getpass.getpass(prompt)
            if strip:
                value = value.strip()
        except getpass.GetPassWarning:
            raise MoodleError("no_secure_prompt", "Терминал не поддерживает скрытый ввод.") from None
    if not value:
        raise MoodleError("empty_secret", "Пустой секрет не принят.")
    SECRETS.add(value)
    return value


def config_path(args):
    return Path(args.config or os.environ.get("MOODLE_CONFIG", DEFAULT_CONFIG)).expanduser()


def read_config(args):
    path = config_path(args)
    data = {}
    if path.exists():
        if os.name != "nt" and path.stat().st_mode & 0o077:
            raise MoodleError("config_permissions", "Файл подключения доступен другим пользователям. Установите права 600.")
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (ValueError, OSError):
            raise MoodleError("invalid_config", "Не удалось прочитать конфигурацию. Повторите setup.") from None
        if not isinstance(data, dict):
            raise MoodleError("invalid_config", "Конфигурация должна быть JSON-объектом.")
    if os.environ.get("MOODLE_TOKEN"):
        data.update(token=os.environ["MOODLE_TOKEN"], site=os.environ.get("MOODLE_URL", data.get("site", DEFAULT_SITE)), mode="api")
    for key in ("token", "ical_url"):
        if data.get(key):
            SECRETS.add(data[key])
    return data


def public_config(site, transport):
    result = transport.json(site + "/lib/ajax/service-nologin.php", payload=[
        {"index": 0, "methodname": "tool_mobile_get_public_config", "args": {}}])
    if not isinstance(result, list) or not result or result[0].get("error"):
        raise MoodleError("public_config_unavailable", "Публичные настройки мобильного API недоступны.")
    data = result[0].get("data", {})
    return {k: data.get(k) for k in ("sitename", "wwwroot", "enablewebservices", "enablemobilewebservice",
                                    "typeoflogin", "maintenanceenabled", "tool_mfa_enabled")}


class API:
    def __init__(self, site, token, transport=None):
        self.site = site_url(site)
        self.token = token
        SECRETS.add(token)
        self.transport = transport or Transport()
        self.functions = None
        self.issues = []
        self.cache = {}
        self.info = self.call("core_webservice_get_site_info")
        self.functions = {f["name"] for f in self.info.get("functions", [])}
        reported = self.info.get("siteurl")
        if reported and site_url(reported) != self.site:
            raise MoodleError("site_mismatch", "Токен ответил для другого адреса сайта. Проверьте канонический URL.")

    def call(self, function, **params):
        if function not in READ_FUNCTIONS:
            raise MoodleError("not_read_only", "Эта функция не входит в список разрешённых операций чтения.")
        if self.functions is not None and function not in self.functions:
            raise MoodleError("missing_function", "Токен не предоставляет " + function)
        key = (function, json.dumps(params, sort_keys=True))
        if key in self.cache:
            return self.cache[key]
        result = self.transport.json(self.site + "/webservice/rest/server.php", {
            **params, "wstoken": self.token, "wsfunction": function, "moodlewsrestformat": "json",
            "moodlewssettingfilter": True, "moodlewssettingfileurl": True,
        })
        if isinstance(result, dict) and result.get("warnings"):
            self.issues.append({"function": function, "warnings": result["warnings"]})
        self.cache[key] = result
        return result

    def optional(self, function, **params):
        try:
            return self.call(function, **params)
        except MoodleError as exc:
            if exc.code in ("invalidtoken", "network_error"):
                raise
            issue = {"function": function, "code": exc.code, "message": str(exc), "scope": params}
            if issue not in self.issues:
                self.issues.append(issue)
            return None

    def courses(self):
        return self.call("core_enrol_get_users_courses", userid=self.info["userid"])

    def select_course(self, query):
        courses = self.courses()
        if str(query).isdigit():
            matches = [c for c in courses if int(c["id"]) == int(query)]
        else:
            q = str(query).casefold()
            matches = [c for c in courses if q in (c.get("fullname", "").casefold(), c.get("shortname", "").casefold())]
            if not matches:
                matches = [c for c in courses if q in (c.get("fullname", "") + " " + c.get("shortname", "")).casefold()]
        if len(matches) != 1:
            names = "; ".join(f"{c['id']}: {c['fullname']}" for c in matches or courses)
            raise MoodleError("ambiguous_course", "Уточните ID или название курса. Доступные варианты: " + names)
        return matches[0]

    def sections(self, courseid):
        return self.call("core_course_get_contents", courseid=courseid)

    def module_data(self, courseid, kind):
        if kind == "assign":
            result = self.optional("mod_assign_get_assignments", courseids=[courseid])
            return None if result is None else [a for c in result.get("courses", []) for a in c.get("assignments", [])]
        if kind not in MODULES:
            return None
        plural = MODULES[kind]
        result = self.optional(f"mod_{kind}_get_{plural}_by_courses", courseids=[courseid])
        return None if result is None else result.get(plural, [])

    def forum(self, forumid):
        result, seen, page = [], set(), 0
        while True:
            data = self.optional("mod_forum_get_forum_discussions", forumid=forumid, page=page, perpage=100)
            if data is None:
                break
            rows = data.get("discussions", [])
            if not rows:
                break
            new = [r for r in rows if r["discussion"] not in seen]
            if not new:
                self.issues.append({"forumid": forumid, "code": "pagination_stalled"})
                break
            for row in new:
                seen.add(row["discussion"])
                posts = self.optional("mod_forum_get_discussion_posts", discussionid=row["discussion"],
                                      sortdirection="ASC", includeinlineattachments=True)
                result.append({**row, "thread": posts})
            page += 1
        return result

    def entries(self, kind, instanceid):
        result, seen, page = [], set(), 0
        while True:
            if kind == "glossary":
                data = self.optional("mod_glossary_get_entries_by_letter", **{
                    "id": instanceid, "letter": "ALL", "from": page * 100, "limit": 100})
            else:
                data = self.optional("mod_data_get_entries", databaseid=instanceid, returncontents=True,
                                     page=page, perpage=100, sort=0, order="ASC")
            if data is None or not data.get("entries"):
                break
            rows = data["entries"]
            new = [row for row in rows if row["id"] not in seen]
            if not new:
                self.issues.append({"type": kind, "instanceid": instanceid, "code": "pagination_stalled"})
                break
            seen.update(row["id"] for row in new)
            result.extend(new)
            page += 1
        return result

    def wiki(self, wikiid):
        result = []
        subwikis = self.optional("mod_wiki_get_subwikis", wikiid=wikiid)
        if subwikis is None:
            return result
        for subwiki in subwikis.get("subwikis", []):
            pages = self.optional("mod_wiki_get_subwiki_pages", wikiid=wikiid,
                                  groupid=subwiki.get("groupid", -1), userid=subwiki.get("userid", 0),
                                  options={"includecontent": 1})
            result.append({"subwiki": subwiki, "pages": pages})
        return result

    def file(self, target):
        target = html.unescape(target)
        if not same_site(self.site, target):
            raise MoodleError("external_file", "Файл находится вне подключённого Moodle. Читайте внешнюю ссылку без токена Moodle.")
        p = url.urlsplit(target)
        relative = p.path[len(url.urlsplit(self.site).path):]
        if relative.startswith("/pluginfile.php"):
            relative = "/webservice" + relative
        if not (relative == "/webservice/pluginfile.php" or relative.startswith("/webservice/pluginfile.php/")):
            raise MoodleError("not_moodle_file", "Ожидалась ссылка pluginfile.php из материалов Moodle.")
        params = [(k, v) for k, v in url.parse_qsl(p.query) if k.lower() not in SECRET_KEYS]
        target = self.site + relative + ("?" + url.urlencode(params) if params else "")
        # Moodle required_param reads POST too: keep tokens out of URLs and proxy URL logs.
        body, mime = self.transport.fetch(target, url.urlencode({"token": self.token}).encode(),
                                          "application/x-www-form-urlencoded", limit=128 * 1024 * 1024)
        if "json" in mime:
            try:
                err = json.loads(body)
                if isinstance(err, dict) and (err.get("errorcode") or err.get("exception")):
                    raise MoodleError("file_unavailable", "Moodle не разрешил скачивание файла.")
            except (ValueError, UnicodeError):
                pass
        if "html" in mime and (b'name="password"' in body or b'id="page-login-index"' in body or b'id="page-error"' in body):
            raise MoodleError("file_login_page", "Вместо файла получена страница входа.")
        return body, mime


class TextHTML(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts, self.links = [], []
        self.skip = 0

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag in ("script", "style"):
            self.skip += 1
        if self.skip:
            return
        if tag in ("p", "div", "br", "tr", "h1", "h2", "h3", "h4", "li"):
            self.parts.append("\n" + ("- " if tag == "li" else ""))
        if tag in ("td", "th"):
            self.parts.append(" | ")
        for attr in ("href", "src"):
            if attrs.get(attr):
                self.links.append(attrs[attr])
        if tag == "img" and attrs.get("alt"):
            self.parts.append("[" + attrs["alt"] + "]")

    def handle_endtag(self, tag):
        if tag in ("script", "style"):
            self.skip = max(0, self.skip - 1)
        elif not self.skip and tag in ("p", "div", "li", "tr", "h1", "h2", "h3", "h4"):
            self.parts.append("\n")

    def handle_data(self, data):
        if not self.skip:
            self.parts.append(data)


def html_data(value):
    p = TextHTML()
    p.feed(value)
    return re.sub(r"\n[ \t]*\n+", "\n\n", "".join(p.parts)).strip(), list(dict.fromkeys(p.links))


def enrich(value):
    if isinstance(value, list):
        return [enrich(v) for v in value]
    if not isinstance(value, dict):
        return value
    result = {k: enrich(v) for k, v in value.items()}
    for key, item in value.items():
        if key in HTML_FIELDS and isinstance(item, str) and item:
            text, links = html_data(item)
            result[key + "_text"] = text
            if links:
                result[key + "_links"] = links
    return result


def materials(value):
    found = {}
    def walk(v):
        if isinstance(v, dict):
            if v.get("fileurl"):
                found[v["fileurl"]] = {k: v[k] for k in ("fileurl", "filename", "filesize", "mimetype", "type") if k in v}
            for x in v.values():
                walk(x)
        elif isinstance(v, list):
            for x in v:
                walk(x)
    walk(value)
    return list(found.values())


def read_module(api, courseid, module, full=False):
    result = {"cmid": module["id"], "courseid": courseid, "name": module.get("name"),
              "type": module.get("modname"), "url": module.get("url"), "module": module}
    if module.get("uservisible") in (False, 0):
        result.update(access="restricted", deadline_state="unverified")
        return enrich(result)
    result["access"] = "available"
    kind = module.get("modname")
    if kind in DEADLINES:
        result["deadline_field"] = DEADLINES[kind]
        result["deadline_label"] = "Срок сдачи" if kind == "assign" else "Окончание приёма/доступа (" + DEADLINES[kind] + ")"
    rows = api.module_data(courseid, kind)
    raw = next((r for r in rows or [] if int(r.get("coursemodule", r.get("cmid", -1))) == int(module["id"])), None)
    if raw is not None:
        result["details"] = raw
    elif kind not in ("label", "resource", "folder"):
        api.issues.append({"cmid": module["id"], "code": "module_details_unavailable", "type": kind})
    if kind == "assign" and raw:
        status = api.optional("mod_assign_get_submission_status", assignid=raw["id"])
        result["submission"] = status
        last = (status or {}).get("lastattempt", {})
        extension = last.get("extensionduedate", 0)
        due = raw.get("duedate")
        result["deadline"] = max(due or 0, extension or 0) or None
        result["deadline_state"] = ("dated" if result["deadline"] else "none") if due is not None else "unverified"
        result["personal_deadline_checked"] = status is not None and "lastattempt" in status
        result["status"] = (last.get("teamsubmission") or last.get("submission") or {}).get("status", "unknown")
    elif kind in DEADLINES:
        due = (raw or {}).get(DEADLINES[kind])
        result["deadline"] = due or None
        result["deadline_state"] = "unverified" if due is None else ("dated" if due else "none")
    if full and kind == "forum" and raw:
        result["discussions"] = api.forum(raw["id"])
    if full and kind in ("glossary", "data") and raw:
        result["entries"] = api.entries(kind, raw["id"])
    if full and kind == "wiki" and raw:
        result["subwikis"] = api.wiki(raw["id"])
    if full and kind in ("book", "page", "label", "resource", "folder", "imscp"):
        texts = []
        for file in materials(result):
            target = file["fileurl"]
            filename = file.get("filename", url.urlsplit(target).path)
            if file.get("type") == "url" or not re.search(r"\.(?:html?|txt|md|csv)$", filename, re.I):
                continue
            try:
                body, mime = api.file(target)
                try:
                    content = body.decode("utf-8-sig")
                except UnicodeDecodeError:
                    api.issues.append({"cmid": module["id"], "code": "text_encoding_unknown", "file": target})
                    continue
                texts.append({"fileurl": target, "mimetype": mime, "content": content})
            except MoodleError as exc:
                api.issues.append({"cmid": module["id"], "file": target, "code": exc.code})
        if texts:
            result["text_files"] = texts
    result["materials"] = materials(result)
    return enrich(result)


def read_course(api, course, full=False, tasks_only=False):
    sections = []
    for section in api.sections(course["id"]):
        rows = []
        for module in section.get("modules", []):
            if not tasks_only or module.get("modname") in DEADLINES:
                rows.append(read_module(api, course["id"], module, full=full))
        sections.append({**section, "modules": rows})
    return {"course": enrich(course), "sections": enrich(sections)}


def period(args, now=None):
    try:
        zone = ZoneInfo(args.timezone)
    except ZoneInfoNotFoundError:
        raise MoodleError("timezone", "Не найдена временная зона. На Windows установите: python -m pip install tzdata") from None
    today = (now or dt.datetime.now(zone)).astimezone(zone).date()
    monday = today - dt.timedelta(days=today.weekday())
    if args.start or args.end:
        if not (args.start and args.end) or args.next_week:
            raise MoodleError("period", "Укажите вместе --from и --to; --next-week используется отдельно.")
        try:
            start = dt.date.fromisoformat(args.start)
            finish = dt.date.fromisoformat(args.end) + dt.timedelta(days=1)
        except ValueError:
            raise MoodleError("period", "Используйте даты YYYY-MM-DD.") from None
    else:
        start = monday + dt.timedelta(days=7 if args.next_week else 0)
        finish = monday + dt.timedelta(days=14)
    if start >= finish:
        raise MoodleError("period", "Конец периода должен быть не раньше начала.")
    return dt.datetime.combine(start, dt.time(), zone), dt.datetime.combine(finish, dt.time(), zone)


def in_period(start, end, timestamp, duration=0):
    timestamp = int(timestamp or 0)
    return start.timestamp() <= timestamp < end.timestamp() or (timestamp < start.timestamp() < timestamp + int(duration or 0))


def stale_deadline_in_period(start, end, timestamp):
    """Project an old Moodle date onto each year touched by a requested period.

    Moodle courses are often reused without changing a due-date year. The
    projection is only a candidate for a current deadline: callers retain the
    source timestamp and must not present it as a confirmed Moodle date.
    """
    try:
        source = dt.datetime.fromtimestamp(int(timestamp), start.tzinfo)
    except (TypeError, ValueError, OSError, OverflowError):
        return None
    current_year = dt.datetime.now(start.tzinfo).year
    if source.year >= current_year:
        return None
    for year in range(start.year, end.year + 1):
        try:
            projected = source.replace(year=year)
        except ValueError:  # February 29 in a non-leap year has no exact annual match.
            continue
        if start <= projected < end:
            return projected
    return None


def list_events(api, args):
    start, end = period(args)
    courses = [api.select_course(args.course)] if args.course else api.courses()
    ids = [c["id"] for c in courses]
    # Legacy endpoint returns the full result (no pagination); group/category permissions are enforced by Moodle.
    calendar = api.optional("core_calendar_get_calendar_events", events={"courseids": ids}, options={
        "timestart": int(start.timestamp()), "timeend": int(end.timestamp()) - 1, "ignorehidden": True,
        "userevents": not bool(args.course), "siteevents": not bool(args.course)})
    events = [e for e in (calendar or {}).get("events", []) if in_period(start, end, e.get("timestart"), e.get("timeduration"))
              and (not args.course or e.get("courseid") in ids)]
    overview = {"period": {"from_inclusive": start.isoformat(), "to_exclusive": end.isoformat(), "timezone": args.timezone},
                "courses": [{"id": c["id"], "name": c["fullname"]} for c in courses], "events": events,
                "tasks": [], "without_deadline": [], "old_dates": [], "stale_deadline_candidates": [],
                "deadline_unverified": [],
                "calendar_available": calendar is not None, "course_inventory_checked": not args.calendar_only,
                "deadline_module_types_checked": sorted(DEADLINES), "other_activities": []}
    index = {}
    if not args.calendar_only:
        for course in courses:
            try:
                for section in api.sections(course["id"]):
                    for module in section.get("modules", []):
                        if module.get("modname") not in DEADLINES:
                            overview["other_activities"].append({"courseid": course["id"], "cmid": module["id"],
                                "name": module.get("name"), "type": module.get("modname"), "url": module.get("url"),
                                "availabilityinfo": module.get("availabilityinfo"), "dates": module.get("dates", []),
                                "note": "Материал курса; наличие задания и срок по содержимому не проверены."})
                data = read_course(api, course, tasks_only=True)
            except MoodleError as exc:
                if exc.code == "invalidtoken":
                    raise
                api.issues.append({"courseid": course["id"], "code": exc.code, "message": str(exc)})
                overview["course_inventory_checked"] = False
                continue
            for section in data["sections"]:
                for task in section["modules"]:
                    task["course_name"] = course["fullname"]
                    task["section_name"] = section.get("name")
                    raw = task.get("details", {})
                    if raw.get("id"):
                        index[(task["type"], raw["id"])] = task
                    state, due = task.get("deadline_state"), task.get("deadline")
                    if state == "unverified":
                        overview["deadline_unverified"].append(task)
                    elif state == "none":
                        overview["without_deadline"].append(task)
                    elif due and in_period(start, end, due):
                        overview["tasks"].append(task)
                    elif due:
                        source_date = dt.datetime.fromtimestamp(due, start.tzinfo)
                        if source_date.year < dt.datetime.now(start.tzinfo).year:
                            overview["old_dates"].append(task)
                            projected = stale_deadline_in_period(start, end, due)
                            if projected:
                                candidate = {**task,
                                    "stale_deadline_source_local": source_date.isoformat(),
                                    "stale_deadline_projected_local": projected.isoformat(),
                                    "stale_deadline_note": "Год срока в Moodle устарел; совпадение дня и месяца с запрошенным периодом не подтверждает срок."}
                                overview["stale_deadline_candidates"].append(candidate)
    for event in events:
        task = index.get((event.get("modulename"), event.get("instance")))
        if task:
            event["task_url"] = task["url"]
            event["cmid"] = task["cmid"]
            # Full condition for opening events or personal/calendar date disagreements too.
            event["task_details"] = task
    overview["events"].sort(key=lambda e: e.get("timestart", 0))
    overview["tasks"].sort(key=lambda e: e.get("deadline", 0))
    overview["stale_deadline_candidates"].sort(key=lambda e: e.get("stale_deadline_projected_local", ""))
    return enrich(overview)


def read_link(api, target):
    if not same_site(api.site, target):
        raise MoodleError("different_site", "Ссылка относится к другому сайту. Выберите его конфигурацию; токен не переслан.")
    p = url.urlsplit(target)
    path = p.path[len(url.urlsplit(api.site).path):]
    query = url.parse_qs(p.query)
    def number(key):
        try:
            return int(query[key][0])
        except (KeyError, ValueError):
            raise MoodleError("invalid_link", "В ссылке отсутствует числовой параметр " + key) from None
    if path == "/course/view.php":
        return read_course(api, api.select_course(str(number("id"))), full=True)
    if path == "/course/section.php":
        sid = number("id")
        for course in api.courses():
            section = next((s for s in api.sections(course["id"]) if s["id"] == sid), None)
            if section:
                return {"course": course, "section": {**section, "modules": [read_module(api, course["id"], m, True) for m in section.get("modules", [])]}}
        raise MoodleError("section_unavailable", "Раздел не найден среди доступных курсов.")
    if path.startswith("/calendar/") and "event" in query:
        event = api.call("core_calendar_get_calendar_event_by_id", eventid=number("event"))
        data = event.get("event", {})
        cmid = data.get("cmid") or (data.get("cm") or {}).get("id")
        if cmid:
            event["activity"] = read_cmid(api, int(cmid))
        return enrich(event)
    if path == "/mod/forum/discuss.php":
        return enrich(api.call("mod_forum_get_discussion_posts", discussionid=number("d"), sortdirection="ASC", includeinlineattachments=True))
    if re.fullmatch(r"/mod/[a-z0-9_]+/view\.php", path):
        return read_cmid(api, number("id"))
    raise MoodleError("unsupported_link", "Поддерживаются ссылки на курс, раздел, элемент курса, обсуждение и calendar/view.php?event=ID.")


def read_cmid(api, cmid):
    info = api.call("core_course_get_course_module", cmid=cmid)["cm"]
    courseid = info["course"]
    for section in api.sections(courseid):
        for module in section.get("modules", []):
            if module["id"] == cmid:
                course = next((c for c in api.courses() if c["id"] == courseid), {"id": courseid})
                return {**read_module(api, courseid, module, full=True), "section_name": section.get("name"), "course": enrich(course)}
    raise MoodleError("module_unavailable", "Элемент отсутствует в доступном содержимом курса.")


def ical_events(args, data, transport):
    try:
        from icalendar import Calendar
        import recurring_ical_events
    except ImportError:
        raise MoodleError("ical_dependency", "Для iCal установите: python3 -m pip install 'icalendar>=6,<7' 'recurring-ical-events>=3,<4'") from None
    start, end = period(args)
    if args.file:
        body = Path(args.file).read_bytes()
        source = "local_snapshot"
    elif data.get("ical_url"):
        body, _ = transport.fetch(data["ical_url"])
        source = "personal_ical_feed"
    else:
        raise MoodleError("not_configured", "Добавьте iCal-ссылку через setup --ical или укажите --file.")
    if b"BEGIN:VCALENDAR" not in body:
        raise MoodleError("not_calendar", "Получен не календарь ICS; проверьте ссылку экспорта.")
    try:
        calendar = Calendar.from_ical(body)
        rows = recurring_ical_events.of(calendar).between(start, end)
    except Exception:
        raise MoodleError("invalid_calendar", "Не удалось разобрать календарь или правила повторения.") from None
    events = []
    for event in rows:
        def stamp(key):
            val = event.decoded(key, None)
            if isinstance(val, dt.datetime):
                return (val if val.tzinfo else val.replace(tzinfo=start.tzinfo)).astimezone(start.tzinfo).isoformat()
            return val.isoformat() if isinstance(val, dt.date) else None
        events.append({"uid": str(event.get("UID", "")), "name": str(event.get("SUMMARY", "")),
                       "description": str(event.get("DESCRIPTION", "")), "start": stamp("DTSTART"), "end": stamp("DTEND"),
                       "last_modified": stamp("LAST-MODIFIED"), "url": str(event.get("URL", "")),
                       "categories": event.get("CATEGORIES").to_ical().decode() if event.get("CATEGORIES") else "",
                       "all_day": not isinstance(event.decoded("DTSTART", None), dt.datetime)})
    return {"source": source, "period": {"from_inclusive": start.isoformat(), "to_exclusive": end.isoformat()},
            "events": events, "coverage": "calendar_only", "limitations": [
                "Диапазон самого экспорта может быть уже запроса; отсутствие событий не доказывает их отсутствие в Moodle.",
                "Задания без дедлайна, состояние сдачи и материалы вне DESCRIPTION не проверены."]}


def setup(args, transport):
    site = site_url(args.site or DEFAULT_SITE)
    timezone = args.timezone
    if args.ical:
        target = secret_prompt("Персональная iCal-ссылка (ввод скрыт): ")
        if not same_site(site, target) or not url.urlsplit(target).path.endswith("/calendar/export_execute.php"):
            raise MoodleError("invalid_ical_url", "Нужна ссылка экспорта календаря с подключаемого Moodle.")
        raw, _ = transport.fetch(target)
        if b"BEGIN:VCALENDAR" not in raw:
            raise MoodleError("not_calendar", "Ссылка не вернула календарь ICS.")
        config = {"site": site, "mode": "ical", "ical_url": target, "timezone": timezone}
        result = {"connected": True, "mode": "calendar_only", "site": site}
    else:
        public = None
        try:
            public = public_config(site, transport)
        except MoodleError:
            pass  # Existing tokens can work even if public discovery is disabled.
        if args.token:
            token = secret_prompt("API-токен Moodle (ввод скрыт): ")
        else:
            if public and (public.get("enablewebservices") == 0 or public.get("enablemobilewebservice") == 0):
                raise MoodleError("mobile_disabled", "На сайте отключён мобильный API. Возможны setup --token для другого сервиса или setup --ical для календаря.")
            if public and public.get("typeoflogin") not in (None, 1):
                raise MoodleError("sso_login", "Сайт использует вход через браузер/SSO. Получите API-токен в настройках Moodle и используйте setup --token.")
            if not sys.stdin.isatty():
                raise MoodleError("interactive_setup", "Запустите setup самостоятельно в обычном терминале.")
            print("Однократное подключение к " + site + ". Пароль не сохраняется.", file=sys.stderr)
            username = input("Логин Moodle: ").strip()
            password = secret_prompt("Пароль Moodle (ввод скрыт): ", strip=False)
            reply = transport.json(site + "/login/token.php", {"username": username, "password": password,
                                   "service": "moodle_mobile_app"}, retry=False)
            token = reply.get("token")
            if not token:
                raise MoodleError("token_missing", "Сервер не выдал токен.")
            del password, reply
        api = API(site, token, transport)
        courses = api.courses()  # A token must actually work before replacing a saved connection.
        config = {"site": site, "mode": "api", "token": token, "timezone": timezone}
        result = {"connected": True, "mode": "api", "site": site, "user": api.info.get("fullname"),
                  "courses": len(courses), "available_read_functions": sorted(api.functions & READ_FUNCTIONS), "public": public}
    private_write(config_path(args), json.dumps(config, ensure_ascii=False).encode())
    result["config_path"] = str(config_path(args))
    return result


def parser():
    p = argparse.ArgumentParser(description="Moodle: события, задания и материалы без браузера.")
    p.add_argument("--config", help="Отдельный файл подключения (также MOODLE_CONFIG)")
    p.add_argument("--output", help="Сохранить полный JSON в файл вместо stdout")
    sub = p.add_subparsers(dest="command", required=True)
    s = sub.add_parser("setup", help="Однократный вход или вставка токена")
    s.add_argument("--site", default=DEFAULT_SITE)
    auth = s.add_mutually_exclusive_group()
    auth.add_argument("--token", action="store_true", help="Вставить имеющийся API-токен скрыто")
    auth.add_argument("--ical", action="store_true", help="Только календарь по персональной ссылке")
    s.add_argument("--timezone", default="Europe/Moscow")
    d = sub.add_parser("doctor", help="Проверить сервер и доступные возможности")
    d.add_argument("--site")
    sub.add_parser("courses", help="Все мои курсы")
    c = sub.add_parser("course", help="Содержимое курса по ID или названию")
    c.add_argument("course")
    c.add_argument("--full", action="store_true", help="Условия, статусы, обсуждения и текстовые материалы")
    r = sub.add_parser("read", help="Прочитать ссылку Moodle полностью")
    r.add_argument("url")
    for command in ("events", "ical"):
        e = sub.add_parser(command, help="События за текущую и следующую календарные недели")
        e.add_argument("--from", dest="start", help="Первый день YYYY-MM-DD")
        e.add_argument("--to", dest="end", help="Последний день YYYY-MM-DD, включительно")
        e.add_argument("--next-week", action="store_true")
        e.add_argument("--timezone", default=None)
        if command == "events":
            e.add_argument("--course")
            e.add_argument("--calendar-only", action="store_true", help="Без проверки заданий вне календаря")
        else:
            e.add_argument("--file", help="Локальный ICS-снимок")
    f = sub.add_parser("file", help="Скачать вложение Moodle без браузера")
    f.add_argument("url")
    f.add_argument("--dest", required=True, help="Новый локальный файл (существующий не перезаписывается)")
    return p


def run(args):
    transport = Transport()
    if args.command == "setup":
        return setup(args, transport)
    config = read_config(args)
    if hasattr(args, "timezone"):
        args.timezone = args.timezone or config.get("timezone", "Europe/Moscow")
    if args.command == "doctor":
        site = site_url(args.site or config.get("site", DEFAULT_SITE))
        result = {"site": site, "connected": False}
        try:
            result["public"] = public_config(site, transport)
        except MoodleError as exc:
            result["public_check_error"] = {"code": exc.code, "message": str(exc)}
        if config.get("token") and site == config.get("site"):
            api = API(site, config["token"], transport)
            result.update(connected=True, user=api.info.get("fullname"),
                          available_read_functions=sorted(api.functions & READ_FUNCTIONS),
                          unavailable_read_functions=sorted(READ_FUNCTIONS - api.functions),
                          courses=len(api.courses()))
        elif config.get("mode") == "ical":
            result["mode"] = "calendar_only"
        elif "public_check_error" in result:
            raise MoodleError("public_check_failed", "Не удалось проверить публичные настройки Moodle. Проверьте сеть и адрес.")
        return result
    if args.command == "ical":
        return ical_events(args, config, transport)
    if not config.get("token"):
        raise MoodleError("not_connected", "API ещё не подключён. Один раз запустите: python3 scripts/moodle.py setup. Для iCal используйте команду ical.")
    api = API(config["site"], config["token"], transport)
    if args.command == "courses":
        data = enrich(api.courses())
    elif args.command == "course":
        course = api.select_course(args.course)
        data = read_course(api, course, full=True) if args.full else {"course": enrich(course), "sections": enrich(api.sections(course["id"]))}
    elif args.command == "read":
        data = read_link(api, args.url)
    elif args.command == "events":
        data = list_events(api, args)
    elif args.command == "file":
        body, mime = api.file(args.url)
        private_write(args.dest, body, overwrite=False)
        data = {"path": str(Path(args.dest).resolve()), "bytes": len(body), "mimetype": mime}
    else:
        raise MoodleError("command", "Неизвестная команда.")
    return {"source": api.site, "retrieved_at": dt.datetime.now(UTC).isoformat(),
            "timezone": getattr(args, "timezone", None) or config.get("timezone", "Europe/Moscow"),
            "data": local_dates(data, getattr(args, "timezone", None) or config.get("timezone", "Europe/Moscow")),
            "issues": api.issues, "coverage": "partial" if api.issues else "available_api_data",
            "scope_note": "Возвращены данные, доступные аккаунту через API. Вложения требуют чтения файлов; внешние ресурсы — отдельного доступа."}


def local_dates(value, timezone):
    fields = {"deadline", "duedate", "extensionduedate", "allowsubmissionsfromdate", "cutoffdate", "gradingduedate",
              "timestart", "timeend", "timeopen", "timeclose", "timemodified", "timecreated", "gradeddate",
              "submissionstart", "submissionend", "assessmentstart", "assessmentend", "timeavailablefrom", "timeavailableto"}
    if isinstance(value, list):
        return [local_dates(x, timezone) for x in value]
    if isinstance(value, dict):
        result = {k: local_dates(v, timezone) for k, v in value.items()}
        for k in fields & value.keys():
            if isinstance(value[k], (int, float)) and value[k] > 0:
                result[k + "_local"] = dt.datetime.fromtimestamp(value[k], ZoneInfo(timezone)).isoformat()
        return result
    return value


def main():
    args = parser().parse_args()
    try:
        result = run(args)
        text = json.dumps(clean(result), ensure_ascii=False, indent=2) + "\n"
        if args.output:
            private_write(args.output, text.encode(), overwrite=False)
            print(json.dumps({"saved": str(Path(args.output).resolve())}, ensure_ascii=False))
        else:
            print(text, end="")
        return 0
    except MoodleError as exc:
        print(json.dumps(clean({"error": exc.code, "message": str(exc)}), ensure_ascii=False), file=sys.stderr)
        return 2
    except (OSError, ValueError, KeyError, TypeError):
        print(json.dumps({"error": "invalid_data_or_file", "message": "Не удалось обработать файл или ответ сервера. Секреты и тело ответа не выводятся."}, ensure_ascii=False), file=sys.stderr)
        return 2
    except (KeyboardInterrupt, EOFError):
        print("Подключение/чтение прервано.", file=sys.stderr)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
