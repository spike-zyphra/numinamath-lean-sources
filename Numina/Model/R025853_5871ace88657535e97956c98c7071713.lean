import Mathlib

theorem algebra_175225 (x : ℝ) (hx : x ≠ 2) :
    x - 5 = 3 * abs (x - 2) / (x - 2) ↔ x = 8 := by
  constructor
  · -- Forward: From the equation prove x=8
    intro h
    have h1 : x - 2 ≠ 0 := by
      intro h2
      apply hx
      linarith
    have h4 : (x - 5) * (x - 2) = 3 * abs (x - 2) := by
      have h5 : x - 2 ≠ 0 := h1
      field_simp [h5] at h ⊢
      linarith
    by_cases h5 : x - 2 ≥ 0
    · -- Assume x ≥ 2
      -- Then |x-2|=x-2
      have h6 : abs (x - 2) = x - 2 := by
        rw [abs_of_nonneg h5]
      rw [h6] at h4
      have h7 : (x - 2) * (x - 8) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h7) with h8 h9
      · -- Assume x -2 =0, so x=2.
        exfalso
        apply hx
        linarith
      · -- Assume x -8 =0, so x=8.
        linarith
    · -- Assume x < 2
      -- Then |x-2|=2-x
      have h8 : abs (x - 2) = (2 - x) := by
        rw [abs_of_neg (show x - 2 < (0 : ℝ) by linarith)]
        all_goals linarith
      rw [h8] at h4
      -- Expanding (x -5)(x -2) = 3*(2 -x).
      have h9 : (x - 2) ^ 2 = 0 := by
        nlinarith
      -- This simplifies to (x -2)^2 =0.
      have h10 : x - 2 = 0 := by
        apply pow_eq_zero 
        exact h9
      -- Solving: x =2.
      -- which created contradiction.
      exfalso
      apply hx
      linarith
  · -- Backward: if x=8 then the equation holds
    intro h
    rw [h]
    norm_num [abs_of_nonneg]