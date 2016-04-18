add_library(runtime OBJECT cpp/lean_runtime.cpp)

FILE(GLOB LEAN_API_INCLUDE_FILES cpp/lean*.h)
install(FILES ${LEAN_API_INCLUDE_FILES} DESTINATION include)
