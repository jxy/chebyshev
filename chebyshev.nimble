# Package

version       = "0.2.2"
author        = "Xiao-Yong Jin"
description   = "Chebyshev approximation."
license       = "MIT"

# Dependencies

requires "nim >= 0.16.0"

task test, "Run test":
  --define: release
  --run
  setCommand "c", "chebyshev.nim"
