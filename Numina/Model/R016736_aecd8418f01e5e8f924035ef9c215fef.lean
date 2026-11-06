import Mathlib

theorem algebra_234121 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x : ℝ, a * x ^ 2 + b * x + c ≠ x) :
    ∀ x : ℝ, a * (a * x ^ 2 + b * x + c) ^ 2 + b * (a * x ^ 2 + b * x + c) + c ≠ x := by
  intro x
  intro hx
  have h1 : a * (a * x ^ 2 + b * x + c) ^ 2 + b * (a * x ^ 2 + b * x + c) + c = x := by
    linarith
  have eq3 : (a * x ^ 2 + b * x + c - x) * (a * (a * x ^ 2 + b * x + c + x) + b + 1) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha)]
  cases' (mul_eq_zero.mp eq3) with h2 h3
  ·
    have h_eq : a * x ^ 2 + b * x + c = x := by linarith
    have hne := h x
    tauto
  ·
    have h4 : a ^ 2 * x ^ 2 + (a * b + a) * x + (a * c + b + 1) = 0 := by
      nlinarith
    have h5 : (a * b + a) ^ 2 - 4 * a ^ 2 * (a * c + b + 1) ≥ 0 := by
      nlinarith [sq_nonneg (a * x ^ 2 + (a * b + a) * x + (a * c + b + 1)), sq_nonneg (a * x + (b + 1) / 2), sq_pos_of_ne_zero ha, sq_nonneg (x * a + (b + 1) / 2)]
    have h8 : (a * b + a) ^ 2 - 4 * a ^ 2 * (a * c + b + 1) < (0 : ℝ) := by
      have h9 : (b - 1) ^ 2 - 4 * a * c < (0 : ℝ) := by
        by_contra h10
        push_neg at h10
        have h11 : ∃ x0 : ℝ, a * x0 ^ 2 + (b - 1) * x0 + c = (0 : ℝ) := by
          use (- (b - 1) + Real.sqrt ((b - 1) ^ 2 - 4 * a * c)) / (2 * a)
          field_simp [ha]
          nlinarith [Real.sqrt_nonneg ((b - 1) ^ 2 - 4 * a * c), Real.sq_sqrt (show (0 : ℝ) ≤ (b - 1) ^ 2 - 4 * a * c by linarith)]
        rcases h11 with ⟨x0, hx0⟩
        have h_eq0 : a * x0 ^ 2 + b * x0 + c = x0 := by linarith
        have hne0 := h x0
        tauto
      nlinarith [sq_pos_of_ne_zero ha]
    linarith