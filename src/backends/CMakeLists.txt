add_library(backends OBJECT
            used_names.cpp
            simple_expr.cpp
            free_vars.cpp
            backend.cpp
            cpp_backend.cpp
            init_module.cpp
            c_emitter.cpp
            clike_backend.cpp
            config.cpp)
