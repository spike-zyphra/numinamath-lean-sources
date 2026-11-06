import Mathlib

open Real

theorem number_theory_6993 : 6.403100 < Real.sqrt 41 ∧ Real.sqrt 41 < 6.403125 := by
  have h1 : 6.403100 < Real.sqrt 41 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h2 : Real.sqrt 41 < 6.403125 := by
    rw [Real.sqrt_lt] <;> norm_num
  exact ⟨h1, h2⟩