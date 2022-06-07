add_llvm_library(LLVMUserLevelInterrupt
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

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms

  DEPENDS
  intrinsics_gen
  )
