import Mathlib

theorem algebra_36352 {a b c : ℝ} (ha : a ≠ b) (h1 : a ^ 2 * (b + c) = 2023) (h2 : b ^ 2 * (c + a) = 2023) :
    c ^ 2 * (a + b) = 2023 := by
  have h3 : a ^ 2 * (b + c) - b ^ 2 * (c + a) = 0 := by linarith 
  have h4 : a ^ 2 * b + a ^ 2 * c - b ^ 2 * c - b ^ 2 * a = 0 := by 
    ring_nf at h3 ⊢
    linarith
  have h5 : (a - b) * (a * b + c * (a + b)) = 0 := by 
    nlinarith
  have h6 : a * b + c * (a + b) = 0 := by
    apply (mul_left_inj' (show a - b ≠ 0 by
      intro h7
      apply ha
      linarith
    )).mp
    linarith
  have h7 : (a + c) * (b + c) = c ^ 2 := by 
    nlinarith [h6]
  have h8 : a ^ 2 * b ^ 2 * ((a + c) * (b + c)) = 2023 ^ 2 := by
    have h9 : a ^ 2 * (b + c) = 2023 := by linarith
    have h10 : b ^ 2 * (a + c) = 2023 := by linarith
    nlinarith
  have h9 : a ^ 2 * b ^ 2 * c ^ 2 = 2023 ^ 2 := by
    rw [show (a + c) * (b + c) = c ^ 2 by linarith [h7]] at h8
    linarith
  have h10 : (a * b * c) ^ 2 = 2023 ^ 2 := by
    nlinarith
  have h11 : a * b * c = 2023 ∨ a * b * c = -2023 := by
    have h12 : (a * b * c) ^ 2 - 2023 ^ 2 = 0 := by
      linarith
    have h13 : (a * b * c - 2023) * (a * b * c + 2023) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h13) with h14 h15
    · -- Case where `a * b * c - 2023 = 0`
      left
      linarith
    · -- Case where `a * b * c + 2023 = 0`
      right
      linarith
  cases' h11 with h12 h13
  · -- Case where `abc = 2023`
    nlinarith [sq_pos_of_ne_zero (show (a - b : ℝ) ≠ 0 by intro h7; apply ha; linarith), h6, sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c)]
  · -- Case where `abc = -2023`
    nlinarith [sq_pos_of_ne_zero (show (a - b : ℝ) ≠ 0 by intro h7; apply ha; linarith), h6, sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c)]