configure_file(lean-settings-installed.el.in lean-settings-installed.el)
FILE(GLOB LEAN_MODE_FILES *.el)
install(FILES ${LEAN_MODE_FILES} "${CMAKE_CURRENT_BINARY_DIR}/lean-settings-installed.el"
        DESTINATION "${EMACS_LISP_DIR}")
