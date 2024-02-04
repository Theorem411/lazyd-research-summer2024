add_llvm_component_library(LLVMULI
  ULIPollingInsertion.cpp
  ULIIntrinsicToExternCall.cpp
  SendUli.cpp
  HandleUli.cpp
  HandleInlets.cpp
  HandleUnwindPoll.cpp
  LazyDTrans.cpp
  EagerDTrans.cpp
  LazyLiveVariable.cpp
  LazyReachingDetachInst.cpp
  LazyReachingStoreReachableLoad.cpp
  InsertLazyDPolling.cpp
  InsertLazyDEnDisUI.cpp
  InstrumentPfor.cpp
  ParallelRegion.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms/ULI

  DEPENDS
  intrinsics_gen
  LLVMLinker

  COMPONENT_NAME
  ULI

  LINK_COMPONENTS
  Analysis
  Core
  IRReader
  Linker
  MC
  Scalar
  Support
  TransformUtils
  Vectorize
  )
