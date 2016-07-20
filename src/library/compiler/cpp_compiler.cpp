    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include "cpp_compiler.h"
#include "kernel/environment.h"
#include "sys/wait.h"

namespace lean {
  process::process(std::string n): m_proc_name(n), m_args() {
      m_args.push_back(m_proc_name);
  }

  process & process::arg(std::string a) {
      m_args.push_back(a);
      return *this;
  }

  void process::run() {
      int pid = fork();
      if (pid == 0) {

          buffer<char*> pargs;
          for (auto arg : m_args) {
              auto str = (char*)malloc(sizeof(char) * 100);
              arg.copy(str, arg.size());
              str[arg.size()] = '\0';
              // std::cout << str << std::endl;
              pargs.push_back(str);
          }

          pargs.data()[pargs.size()] = NULL;

          auto err = execvp(pargs.data()[0], pargs.data());
          if (err < 0) {
              throw std::runtime_error("executing process failed: ...");
          }
      } else if (pid == -1) {
          throw std::runtime_error("forking process failed: ...");
      } else {
          int status;
          waitpid(pid, &status, 0);
      }
  }

  cpp_compiler & cpp_compiler::link(std::string lib) {
      m_link.push_back(lib);
      return *this;
  }

  cpp_compiler & cpp_compiler::library_path(std::string lib_path) {
      m_library_paths.push_back(lib_path);
      return *this;
  }

  cpp_compiler & cpp_compiler::include_path(std::string include_path) {
      m_include_paths.push_back(include_path);
      return *this;
  }

  cpp_compiler & cpp_compiler::debug(bool on) {
      m_debug = on;
      return *this;
  }

  cpp_compiler & cpp_compiler::file(std::string file_path) {
      m_files.push_back(file_path);
      return *this;
  }

  cpp_compiler::cpp_compiler() : m_library_paths(), m_files(), m_include_paths(), m_link(), m_debug(true) {}

  void cpp_compiler::run() {
      process p("g++");
      p.arg("-std=c++11");

      // Add all the library paths.
      for (auto include_path : m_include_paths) {
          std::string arg("-I");
          arg += include_path;
          p.arg(arg);
      }

      // Add all the link paths.
      for (auto link_path : m_library_paths) {
          std::string arg("-L");
          arg += link_path;
          p.arg(arg);
      }

      // Add all the files
      for (auto file_path : m_files) {
          p.arg(file_path);
      }

      // Add all the link arguments.
      for (auto link: m_link) {
          std::string arg("-l");
          arg += link;
          p.arg(arg);
      }

      if (m_debug) {
          p.arg("-g");
      }

      p.run();
  }
}
