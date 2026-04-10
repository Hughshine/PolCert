#!/bin/sh
exec "$(dirname "$0")/polopt" --legacy-generic-tiling "$@"
