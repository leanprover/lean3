-- A special 1-type with a constructor hidden from programmers, it is my intent
-- that this will be one of the few types that the code-generator knows about,
-- allowing the language to use an IO-monad/effect system/some new abstraction
-- in the future.
constant RealWorld : Type
