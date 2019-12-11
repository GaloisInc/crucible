# Crucible Api Usage Checker
This is a first approximation of an NFA based api usage checker in Crucible. It is implemented as a Crucible execution feature and currently specialized to the LLVM front end. As there is not yet a front end NFA api specification language, there are 2 example NFAs hardcoded within the source file. One example checkes for proper function call ordering and the other checks that a function is passed in the return value (`LLVMPointer`) of a previous function. Which NFA is loaded can be configured within the source file. 

## Demo
To demo the functionality, install the `apiCheckExecFeat` execution feature in `Crux` (`Crux.hs`) and then use `CruxLLVMMain.hs` on the provided cpp demo files in the `/test` directory. 

## Assumptions and Limitations
This is a fragile first approximation with many limitations. Future work should consist of:
* A more robust representation of NFA state
* A more robust NFA structure which is able to reason about symbolic values and carry predicates along state transitions
* A specification for driving NFA symbol creation based on the crucible simulator state
* Generalize to multiple front ends 
* Generalize execution feature to take an api usage NFA as input
* Construct an api usage specification language which is parsed in a function override and converted to an appropriate NFA
