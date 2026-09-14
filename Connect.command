#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
python3 scripts/moodle.py setup "$@"
printf '\nПодключение сохранено. Это окно можно закрыть.\n'
