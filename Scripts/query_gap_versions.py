#!/usr/bin/env python3
"""Print the GAP and package versions used by the order-32 generators."""

from generate_order32_cohomology import run_gap
from translate_pc import default_gap_bash, default_gap_exe


def main() -> None:
    gap_bash = default_gap_bash()
    gap_exe = default_gap_exe(gap_bash)
    script = r'''
Print("GAP ", GAPInfo.Version, "\n");
for name in ["smallgrp", "anupq"] do
  info := PackageInfo(name);
  if Length(info) = 0 then
    Print(name, " unavailable\n");
  else
    Print(name, " ", info[1].Version, "\n");
  fi;
od;
QUIT;
'''
    print(run_gap(script, gap_bash, gap_exe), end="")


if __name__ == "__main__":
    main()
