import argparse
import json
from .pipeline import roundtrip


def main():
    parser = argparse.ArgumentParser(description="One-case combinational RTLIL → LeanRTL prototype")
    commands = parser.add_subparsers(dest="command", required=True)
    rt = commands.add_parser("roundtrip", help="local round-trip; Jasper acceptance is separate")
    rt.add_argument("--manifest", required=True)
    rt.add_argument("--out", required=True)
    args = parser.parse_args()
    result = roundtrip(args.manifest, args.out)
    print(json.dumps({"status": result["status"], "out": args.out}, indent=2))


if __name__ == "__main__":
    main()
