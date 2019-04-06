[![Build Status](https://travis-ci.org/kriw/bap-plugins.svg?branch=master)](https://travis-ci.org/kriw/bap-plugins)

- myssa: Simple Implementation of SSA transformation.

- copypropagation: Propagate Assignment (e.g., `x := y; z := x` to `x := y; z := y`).

- mydeadcode: DeadCode elimination, the alogirithm is same to [BinaryAnalysisPlatform/bap-plugins](https://github.com/BinaryAnalysisPlatform/bap-plugins/blob/master/deadcode/deadcode.ml).

- prune ssa: The Set of passes (myssa, copypropagation, mydeadcode). This produces prune ssa.
