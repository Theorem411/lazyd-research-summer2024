add_llvm_library(LLVMUserLevelInterrupt
  ULIPollingInsertion.cpp
  ULIIntrinsicToExternCall.cpp
  SendUli.cpp
  HandleUli.cpp
  HandleInlets.cpp
  HandleUnwindPoll.cpp
  LazyDTrans.cpp
  LazyLiveVariable.cpp
  LazyReachingDetachInst.cpp
  LazyReachingStoreReachableLoad.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms

  DEPENDS
  intrinsics_gen
  )
