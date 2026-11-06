import Mathlib

/-- a) Determine the order of 2 modulo 5  -/
theorem number_theory_4991_a : orderOf (2 : ZMod 5) = 4 := by
  simp [orderOf_eq_iff]
  constructor
  · decide
  · intro m h1 h2
    interval_cases m <;> decide

/-- b) Determine the order of 3 modulo 10  -/
theorem number_theory_4991_b : orderOf (3 : ZMod 10) = 4 := by
  simp [orderOf_eq_iff]
  constructor
  · decide
  · intro m h1 h2
    interval_cases m <;> decide

/-- c) Determine the order of 10 modulo 13  -/
theorem number_theory_4991_c : orderOf (10 : ZMod 13) = 6 := by
  simp [orderOf_eq_iff]
  constructor
  · decide
  · intro m h1 h2
    interval_cases m <;> decide

/-- d) Determine the order of 7 modulo 19  -/
theorem number_theory_4991_d : orderOf (7 : ZMod 19) = 3 := by
  simp [orderOf_eq_iff]
  constructor
  · decide
  · intro m h1 h2
    interval_cases m <;> decide
