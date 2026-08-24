# Third-party notices

## Formal Learning Theory Kernel

The Choquet-capacity scaffold in
`AsymptoticStatistics/ForMathlib/ChoquetCapacity/Basic.lean` and
`AsymptoticStatistics/ForMathlib/ChoquetCapacity/Analytic.lean` adapts work by
Dhruv Gupta from the *Formal Learning Theory Kernel* project, file
`FLT_Proofs/PureMath/ChoquetCapacity.lean`, pinned at commit
`b1b9d16a552e3e09bfbb8151fe6aa14c805d7979`:

https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel/blob/b1b9d16a552e3e09bfbb8151fe6aa14c805d7979/FLT_Proofs/PureMath/ChoquetCapacity.lean

The source is licensed under Apache License 2.0. Its exact repository license text is
preserved in `LICENSES/formal-learning-theory-kernel-Apache-2.0.txt`. The adaptation
splits the original single file into basic and analytic modules, retains its declaration
interfaces, and ports and adapts the proof bodies to the pinned Mathlib version.
