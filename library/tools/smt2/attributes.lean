def smt2_attribute : user_attribute :=
{ name := `smt2,
  descr := "Mark a decalartion as part of the gloabl environment of the smt2 tactic" }

run_cmd register_attribute `smt2_attribute

