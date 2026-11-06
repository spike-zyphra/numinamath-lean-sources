import Mathlib

theorem number_theory_208017 (a : ℤ) (ha : a ≠ 0) :
    ∃ n : ℤ, (2 / a : ℝ) + 5 + Real.sqrt 2 = n ↔ n = 3 ∨ n = 7 := by
  use 5
  have h6 : ¬ ( (2 / (a : ℝ) ) + 5 + Real.sqrt 2 = (5 : ℝ) ) := by 
    by_contra h
    have h3 : Real.sqrt 2 = - ( (2 / (a : ℝ) ) ) := by linarith
    have h10 : Irrational (Real.sqrt (2 : ℝ) ) := by
      native_decide
    have h11 : ¬ Irrational (Real.sqrt (2 : ℝ) ) := by 
      rw [h3]
      simp [Rat.not_irrational]
    contradiction
  simp [h6]