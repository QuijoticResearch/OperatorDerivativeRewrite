"""Live-clock external Git push admission; no clock override or bypass in the CLI."""
import argparse
from datetime import datetime, timezone
import re
import sys
from zoneinfo import ZoneInfo

ZONE = "America/New_York"


def restricted(instant=None):
    instant = datetime.now(timezone.utc) if instant is None else instant
    if instant.tzinfo is None:
        raise ValueError("An aware timestamp is required")
    eastern = instant.astimezone(ZoneInfo(ZONE))
    return eastern.weekday() < 5 and 9 <= eastern.hour < 17


def external(remote):
    """Recognize local drive/POSIX paths; network/unknown transports fail closed."""
    if remote.startswith(("\\\\", "//")):
        return True
    if remote.startswith("file:///"):
        return False
    if re.match(r"^[A-Za-z]:[/\\]", remote) or remote.startswith(("/", "./", "../")):
        return False
    return True


def blocked(remote, instant=None):
    return external(remote) and restricted(instant)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--remote", required=True)
    args = parser.parse_args()
    try:
        if blocked(args.remote):
            print("External push queued: weekdays 09:00–17:00 America/New_York; "
                  "keep the local commit and audit receipt, retry outside this window.",
                  file=sys.stderr)
            return 1
        return 0
    except Exception:
        print("Push refused: unable to verify the America/New_York time policy.", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
