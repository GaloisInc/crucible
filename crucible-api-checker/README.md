# Crucible Api Usage Checker
This is a first approximation of an NFA based api usage checker in Crucible. It is implemented as a Crucible execution feature and currently specialized to the LLVM front end. As there is not yet a front end NFA api specification language, there are 2 example NFAs hardcoded within the source file. One example checkes for proper function call ordering and the other checks that a function is passed in the return value (`LLVMPointer`) of a previous function. Which NFA is loaded can be configured within the source file. 

## Demo
To demo the functionality, install the `apiCheckExecFeat` execution feature in `Crux` (`Crux.hs`) and then use `CruxLLVMMain.hs` on the provided cpp demo files in the `/test` directory. 

## Assumptions and Limitations
* Selecting which argument(s) to monitor and the bookkeeping strategy
  * At call time, check which value on which function
* Concrete value comparison
* 

## Future Work
* Generalize api for multiple front ends
* Generalize to an take NFA for specific api usage as input to the execution feature
  * Nfa for each api Usage
* Specification language
  * Take in NFA spec language from custom override
