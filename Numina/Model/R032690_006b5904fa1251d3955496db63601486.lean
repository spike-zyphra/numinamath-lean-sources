import Mathlib

theorem number_theory_276246 : ¬ ∃ (x : ℚ), Real.sqrt 2 = x := by
  rintro ⟨x, hx⟩
  have h2 : Irrational (Real.sqrt 2) := by
    apply irrational_sqrt_two
  have h3 : ¬ Irrational (Real.sqrt 2) := by
    rw [hx]
    simp
  contradiction