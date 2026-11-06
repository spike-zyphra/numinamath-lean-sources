import Mathlib

theorem algebra_142907 {R1 R2 : ℝ} (hsum : R1 + R2 = 35) (hq : 2 / 5 = R1 / R2) :
    R1 = 10 ∧ R2 = 25 := by
  have h1 : R1 = 10 := by
    have h2 : R2 ≠ 0 := by
      by_contra h
      rw [h] at hq
      norm_num at hq
      all_goals linarith
    field_simp [h2] at hq
    linarith
  have h2 : R2 = 25 := by
    linarith [hsum, h1]
  exact ⟨h1, h2⟩