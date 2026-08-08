#!/usr/bin/env bash

# Shared resource detection for CI build and test orchestration.

ci_detect_cores() {
  local cores quota period quota_cores
  cores="$(getconf _NPROCESSORS_ONLN 2>/dev/null || nproc 2>/dev/null || printf '1')"
  if ! [[ "$cores" =~ ^[1-9][0-9]*$ ]]; then
    cores=1
  fi

  quota=0
  period=0
  if [[ -r /sys/fs/cgroup/cpu.max ]]; then
    read -r quota period </sys/fs/cgroup/cpu.max
  elif [[ -r /sys/fs/cgroup/cpu/cpu.cfs_quota_us ]] \
      && [[ -r /sys/fs/cgroup/cpu/cpu.cfs_period_us ]]; then
    quota="$(cat /sys/fs/cgroup/cpu/cpu.cfs_quota_us)"
    period="$(cat /sys/fs/cgroup/cpu/cpu.cfs_period_us)"
  fi
  if [[ "$quota" =~ ^[0-9]+$ ]] && [[ "$period" =~ ^[1-9][0-9]*$ ]] \
      && ((quota > 0)); then
    quota_cores=$(((quota + period - 1) / period))
    if ((quota_cores < cores)); then
      cores=$quota_cores
    fi
  fi

  printf '%s\n' "$cores"
}

ci_detect_memory_mb() {
  local host_kb host_mb cgroup_limit cgroup_used cgroup_mb

  host_kb="$(awk '
    /^MemAvailable:/ { print $2; found=1; exit }
    /^MemTotal:/ { fallback=$2 }
    END { if (!found) print fallback }
  ' /proc/meminfo 2>/dev/null)"
  if ! [[ "$host_kb" =~ ^[0-9]+$ ]]; then
    host_kb=0
  fi
  host_mb=$((host_kb / 1024))

  cgroup_mb=0
  if [[ -r /sys/fs/cgroup/memory.max ]]; then
    cgroup_limit="$(cat /sys/fs/cgroup/memory.max)"
    cgroup_used="$(cat /sys/fs/cgroup/memory.current 2>/dev/null || printf '0')"
  elif [[ -r /sys/fs/cgroup/memory/memory.limit_in_bytes ]]; then
    cgroup_limit="$(cat /sys/fs/cgroup/memory/memory.limit_in_bytes)"
    cgroup_used="$(cat /sys/fs/cgroup/memory/memory.usage_in_bytes 2>/dev/null || printf '0')"
  else
    cgroup_limit=max
    cgroup_used=0
  fi

  if [[ "$cgroup_limit" =~ ^[0-9]+$ ]] && [[ "$cgroup_used" =~ ^[0-9]+$ ]] \
      && ((cgroup_limit > cgroup_used)); then
    cgroup_mb=$(((cgroup_limit - cgroup_used) / 1024 / 1024))
  fi

  if ((host_mb == 0)); then
    host_mb=$cgroup_mb
  elif ((cgroup_mb > 0 && cgroup_mb < host_mb)); then
    host_mb=$cgroup_mb
  fi

  if ((host_mb < 1)); then
    host_mb=1
  fi
  printf '%s\n' "$host_mb"
}

ci_choose_jobs() {
  local override_name="$1"
  local max_jobs="$2"
  local memory_per_job_mb="$3"
  local cores memory_mb memory_jobs requested jobs

  if ! [[ "$max_jobs" =~ ^[1-9][0-9]*$ ]]; then
    printf 'invalid maximum job count: %q\n' "$max_jobs" >&2
    return 2
  fi
  if ! [[ "$memory_per_job_mb" =~ ^[1-9][0-9]*$ ]]; then
    printf 'invalid memory-per-job value: %q\n' "$memory_per_job_mb" >&2
    return 2
  fi

  cores="$(ci_detect_cores)"
  memory_mb="$(ci_detect_memory_mb)"
  memory_jobs=$((memory_mb / memory_per_job_mb))
  if ((memory_jobs < 1)); then
    memory_jobs=1
  fi

  requested="${!override_name:-auto}"
  if [[ "$requested" == auto || -z "$requested" ]]; then
    jobs=$cores
  elif [[ "$requested" =~ ^[1-9][0-9]*$ ]]; then
    jobs=$requested
  else
    printf 'invalid %s=%q; expected auto or a positive integer\n' \
      "$override_name" "$requested" >&2
    return 2
  fi

  if ((jobs > cores)); then
    jobs=$cores
  fi
  if ((jobs > memory_jobs)); then
    jobs=$memory_jobs
  fi
  if ((jobs > max_jobs)); then
    jobs=$max_jobs
  fi
  if ((jobs < 1)); then
    jobs=1
  fi
  printf '%s\n' "$jobs"
}

ci_run_timed() {
  local label="$1"
  shift
  local started finished
  started="$(date +%s)"
  printf '[ci-timing] START %s\n' "$label"
  "$@"
  finished="$(date +%s)"
  printf '[ci-timing] END %s wall=%ss\n' "$label" "$((finished - started))"
}
