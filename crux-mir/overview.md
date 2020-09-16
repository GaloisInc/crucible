* Mir-verifier module structure

** src/Mir/DefId.hs

    data structure for working with Ids from mir-json

** src/Mir/Mir.hs
   
    ADT definitions for MIR

** src/Mir/JSON.hs

    parser for mir-json
     
** src/Mir/PP.hs

    display Mir AST 

** src/Mir/GenericOps.hs

    Mir AST syntax transformations defined using GHC.Generics
    
** src/Mir/MirTy.hs

    operations related to Mir type system

** src/Mir/Pass/Pass.hs
  toplevel module for mir-to-mir AST transformations
  these transformations provide additional information to the AST and elaborate
  hard to translate code patterns

*** src/Mir/Pass/NoMutParams.hs
  create new local variables that correspond to mut function arguments
    
*** src/Mir/Pass/AllocateEnum.hs
  replace a sequence of enum inits with an aggregate call
	 
*** src/Mir/Pass/AssociatedTypes.hs
  remove "TyProjection" from Mir AST

*** src/Mir/Pass/ExpandSuperTraits.hs
  inherit all items from super traits

Rest of these are not currently used:

*** src/Mir/Pass/MutRefReturnStatic.hs
*** src/Mir/Pass/RemoveBoxNullary.hs
*** src/Mir/Pass/RemoveStorage.hs
*** src/Mir/Pass/CollapseRefs.hs    
*** src/Mir/Pass/RewriteMutRef.hs
  eliminates in/out argument passing via mutable references
  rewrites functions to take & return owned arguments
  TODO: remove dependence on Mir.Trans
	  
** src/Mir/Intrinsics.hs

    mir specific primitives for specialization, defined via crucible syntax extension
    - MirReference
    - MirSlice

** src/Mir/Overrides.hs (bindFn)

    create overrides for symbolic execution

** src/Mir/Generator.hs

    definition of generator state (FnState, CollectionState) and type (MirGenerator)
    used for translation
    
** src/Mir/TransTy.hs      (type translations)
   src/Mir/Trans.hs        (main MIR translation --- see transCollection)
   src/Mir/TransCustom.hs  (implementation of custom operations)

    main translation from Mir AST to Crucible CFG

** src/Mir/Generate.hs (generateMIR, translateMIR, translateAll, loadPrims)
    -- run mir-json on a rust crate
    -- rewrite & translate Mir to Crucible CFG
    -- load & translate the MIR library 

** src/Mir/Language.hs

   crux-based simulator harness

** src/Mir/Run.hs (extractFromCFGPure)
   
   used by SAW interface
   somewhat defunct, hasn't been tested recently

** src/Mir/SAWInterface.hs (loadMIR, extractMIR)

   SAW interface, produce a saw-core Term 
   somewhat defunct, hasn't been tested recently


* testing is in test/Test.hs 
