import Mathlib

theorem inequalities_322367 (a b c : ℝ) (ha : a ≠ 0) (hroots : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0) :
    (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ (9 / 8) * a ^ 2 := by
  rcases hroots with ⟨x1, x2, hx12, hx1, hx2⟩

  have h1 : a * x1 ^ 2 + b * x1 + c = 0 := hx1
  have h2 : a * x2 ^ 2 + b * x2 + c = 0 := hx2
  have h3 : x1 ≠ x2 := hx12
  have h4 : a * (x1 + x2) + b = 0 := by
    have h5 : (x1 - x2) ≠ 0 := by
      intro h6
      apply h3
      linarith
    have h6 : a * (x1 ^ 2 - x2 ^ 2) + b * (x1 - x2) = 0 := by
      nlinarith [h1, h2]
    have h7 : a * (x1 + x2) + b = 0 := by
      apply (mul_left_inj' h5).mp
      linarith
    linarith

  have h5 : a * (x1 * x2) = c := by
    nlinarith [h1, h2, h4, sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
      intro h6
      apply h3
      linarith
    )]

  have h8 : b = -a * (x1 + x2) := by
    linarith [h4]

  have h9 : c = a * (x1 * x2) := by
    linarith [h5]

  have eq1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = a ^ 2 * ((1 + x1 + x2) ^ 2 + (x1 + x2 + x1 * x2) ^ 2 + (x1 * x2 - 1) ^ 2) := by 
    rw [h8, h9]
    ring

  have h11 : (1 + x1 + x2) ^ 2 + (x1 + x2 + x1 * x2) ^ 2 + (x1 * x2 - 1) ^ 2 ≥ 9 / 8 := by
    nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 + 3 / 4), sq_nonneg (x1 * x2 - 1 / 4), sq_nonneg (x1 + x2 - 2 * x1 * x2), sq_nonneg ((x1 + x2) * x1 * x2 + 1 / 4)]

  have h12 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ (9 / 8) * a ^ 2 := by
    have h13 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = a ^ 2 * ((1 + x1 + x2) ^ 2 + (x1 + x2 + x1 * x2) ^ 2 + (x1 * x2 - 1) ^ 2) := eq1
    rw [h13]
    nlinarith [sq_pos_of_ne_zero ha, h11]

  exact h12