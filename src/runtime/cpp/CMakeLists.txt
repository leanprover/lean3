add_library(runtime OBJECT lean_runtime.cpp)

FILE(GLOB LEAN_API_INCLUDE_FILES lean*.h)
install(FILES ${LEAN_API_INCLUDE_FILES} DESTINATION include)
