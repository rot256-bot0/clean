import Witgen.Primality

open Witgen.Primality
example : checkTrace 17 2 1 [(10, 4)] = true := by decide
example : (2 : ZMod 17) ^ 10 = 4 :=
  trace_power 17 2 10 4 [(10,4)] (by decide) (by decide) (by decide)
example : (3 : ZMod 65537) ^ 65536 = 1 :=
  trace_power 65537 3 65536 1 [(1,3),(0,54449),(0,282),(0,64),(0,1)]
    (by decide) (by decide) (by decide)
example : checkTrace 17 2 1 [(10, 5)] = false := by decide
