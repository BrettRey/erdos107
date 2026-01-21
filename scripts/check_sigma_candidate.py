#!/usr/bin/env python3
from __future__ import annotations

import os
import runpy


def main() -> None:
    here = os.path.dirname(__file__)
    target = os.path.join(here, "check_sigma.py")
    runpy.run_path(target, run_name="__main__")


if __name__ == "__main__":
    main()
