import Mathlib

theorem algebra_187429 {p : ℝ} (h : ∃ x y, x ≠ y ∧ x^2 + p * x - 16 = 0 ∧ y^2 + p * y - 16 = 0 ∧ x / y = -4) :
    p = 6 ∨ p = -6 := by

  rcases h with ⟨x, y, hxy, hx, hy, hxyr⟩

  have hyne : y ≠ 0 := by
    by_contra h'
    rw [h'] at hxyr
    norm_num at hxyr
    all_goals
      try { tauto }
      try { linarith }
    all_goals try nlinarith

  have h2 : x = -4 * y := by
    have : y ≠ 0 := hyne
    field_simp [this] at hxyr
    nlinarith -- could also fix linarith in processing here

  rw [h2] at hx

  have eq1 : (-4 * y) ^ 2 + p * (-4 * y) - 16 = 0 := by
    linarith

  have eq2 : y ^ 2 + p * y - 16 = 0 := by
    linarith

  have eq3 : y^2 = 4 := by
    nlinarith [sq_nonneg (y + 2), sq_nonneg (y - 2), sq_nonneg (p), sq_nonneg (p + 6), sq_nonneg (p - 6), sq_pos_of_ne_zero (show y ≠ 0 by assumption)]

  have h3 : y = 2 ∨ y = -2 := by
    have h4 : y^2 = 4 := eq3
    have : y^2 -4 = 0 := by nlinarith
    have : (y -2) * (y + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 this) with h5 h6
    · -- case y=2
      left
      linarith
    · -- case y=-2
      right
      linarith

  cases h3 with
  | inl h5 =>
    have hp : p = 6 := by
      rw [h5] at hy
      nlinarith
    left
    linarith

  | inr h5 =>
    have hp : p = -6 := by
      rw [h5] at hy
      nlinarith
    right
    linarith
  all_goals try { tauto }