import Mathlib

theorem number_theory_7135 : ¬ ∃ n : ℚ, Real.sqrt 2 = n := by 
  intro h
  rcases h with ⟨q, hq⟩
  have h1 : Irrational (Real.sqrt 2) := by
    native_decide
  have h2 : ¬ Irrational (Real.sqrt 2) := by
    rw [show Real.sqrt 2 = (q : ℝ) by linarith [hq]]
    simp
  contradiction