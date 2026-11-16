"""CLI for source Verilog -> checked LeanRTL, without round-trip or Jasper."""
import argparse
import json

from .pipeline import import_verilog


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--out", required=True)
    parser.add_argument("--framework-root", help="Lake workspace containing LeanRTL")
    parser.add_argument("--no-build-framework", action="store_true")
    args = parser.parse_args()
    result = import_verilog(args.manifest, args.out,
                            build_framework=not args.no_build_framework,
                            framework_root=args.framework_root)
    print(json.dumps({"status": result["status"], "out": args.out}, indent=2))


if __name__ == "__main__":
    main()
