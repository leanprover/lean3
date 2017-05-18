/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include "kernel/environment.h"
#include "library/module.h"
#include "library/module_mgr.h"
#include "util/optional.h"
#include "util/lean_path.h"

// This function is intended to "auto-import" certain namespaces.
//
// This is useful for the native compiler, as it allows us to ensure
// the compiler has been loaded before attempting to invoke it from
// C++.
lean::environment auto_import_tools(
    lean::module_mgr & mod_mgr,
    std::shared_ptr<const lean::module_info> current_mod,
    lean::name & import_name)
{
    // Hang on to the current module's environment.
    auto env = current_mod->get_produced_env();

    // Resolve the module to import.
    lean::module_name to_import_mod_name = { import_name , lean::optional<unsigned>() };
    lean::module_id mod = lean::resolve(mod_mgr.m_path, "tools/native", to_import_mod_name);
    auto mod_to_import = mod_mgr.get_module(mod);

    // Copy the set of dependencies and add the module to import to the list.
    auto deps = current_mod->m_deps;
    deps.push_back(lean::module_info::dependency { mod_to_import->m_mod, { import_name , lean::optional<unsigned>()}, mod_to_import });

    // Build a loader from the current module.
    auto loader = mk_loader(current_mod->m_mod, deps);

    // Finally add the module name we want to import, and then import into the environment, building a new one with the module imported and return it.
    std::vector<lean::module_name> imports;
    imports.push_back({ import_name, lean::optional<unsigned>()});
    return import_modules(env, current_mod->m_mod, imports, loader);
}
