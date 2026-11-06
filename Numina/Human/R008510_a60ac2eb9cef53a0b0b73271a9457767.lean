import Mathlib

/- Determine which of the following integers are prime numbers:
a) 101
b) 103
c) 107
d) 111
e) 113
f) 121. -/
theorem number_theory_4484 :
    Nat.Prime 101 ∧ Nat.Prime 103 ∧ Nat.Prime 107 ∧
    ¬Nat.Prime 111 ∧ Nat.Prime 113 ∧ ¬Nat.Prime 121:= by
  -- verify by computation
  decide
