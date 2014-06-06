# Python Binding Tests
file(GLOB PYTESTS "${LEAN_SOURCE_DIR}/../tests/python/*.py")
FOREACH(T ${PYTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "pytest_${T_NAME}"
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/python"
    COMMAND "./test_single.sh" "${PYTHON_EXECUTABLE}" ${T_NAME})
  # Set Label
  set_tests_properties("pytest_${T_NAME}" PROPERTIES LABELS "python")
  # Set ENV Variable "PYTHONPATH"
  set_tests_properties("pytest_${T_NAME}" PROPERTIES ENVIRONMENT "PYTHONPATH=${LEAN_BINARY_DIR}")
ENDFOREACH(T)
