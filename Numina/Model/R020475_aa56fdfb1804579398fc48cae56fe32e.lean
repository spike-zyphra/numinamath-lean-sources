import Mathlib

theorem number_theory_101344 (x y : ℕ) :
    x * (x + 1) = 4 * y * (y + 1) ↔ (x, y) = (0, 0) := by
  constructor
  · -- Assume x * (x + 1) = 4 * y * (y + 1), prove (x, y) = (0, 0)
    intro h
    have h1 : x ≤ 2 * y := by
      by_contra h2
      push_neg at h2
      have h2 : x ≥ 2 * y + 1 := by omega
      nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (x + 1 - 2 * (y + 1)), sq_nonneg (y), sq_nonneg (x), h]
    -- Show x = 2y
    have h3 : x = 2 * y := by
      nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (x + 1 - 2 * (y + 1)), h]
    -- Show y = 0
    have h4 : y = 0 := by
      rw [show x = 2 * y by linarith] at h
      nlinarith [sq_nonneg (y), sq_nonneg (2 * y), sq_nonneg (y + 1)]
    -- Show x = 0
    have h8 : x = 0 := by
      linarith [h4, h3]
    simp [Prod.ext_iff, h8, h4]
  · -- Assume (x, y) = (0, 0), prove x * (x + 1) = 4 * y * (y + 1)
    rintro ⟨rfl, rfl⟩
    all_goals norm_num