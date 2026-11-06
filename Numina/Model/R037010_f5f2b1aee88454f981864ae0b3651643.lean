import Mathlib

theorem number_theory_172536 (k : ℝ) (hk : Irrational k) (ε : ℝ) (hε : ε > 0) :
    ∃ m n : ℤ, |(k * m - n)| / Real.sqrt (k ^ 2 + 1) < ε := by

  use 0
  use 0

  have h1 : |(k * (0:ℤ) - (0:ℤ))| = (0:ℝ) := by
    simp

  have h2 : Real.sqrt (k ^ 2 + 1) > 0 := by
    apply Real.sqrt_pos.mpr
    have h1 : k ^ 2 + 1 > 0 := by
      nlinarith [sq_nonneg k]
    linarith

  have h3 : |(k * (0:ℤ) - (0:ℤ))| / Real.sqrt (k ^ 2 + 1) = (0:ℝ) := by
    rw [h1]
    norm_num
  rw [h3]
  all_goals linarith [hε]