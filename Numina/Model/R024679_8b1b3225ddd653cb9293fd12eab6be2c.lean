import Mathlib

theorem algebra_137063 {a b c : ℝ} (h₀ : a ≠ -b) (h₁ : b ≠ -c) (h₂ : c ≠ -a)
    (h₃ : (a * b) / (a + b) = 4) (h₄ : (b * c) / (b + c) = 5) (h₅ : (c * a) / (c + a) = 7) :
    (a * b * c) / (a * b + b * c + c * a) = 280 / 83 := by
  have h6 : a + b ≠ 0 := by
    intro h
    apply h₀
    linarith
  have h7 : b + c ≠ 0 := by
    intro h
    apply h₁
    linarith
  have h8 : c + a ≠ 0 := by
    intro h
    apply h₂
    linarith
  have eq1 : a * b = 4 * (a + b) := by
    have h6' : a + b ≠ 0 := h6
    field_simp [h6'] at h₃
    linarith
  have eq2 : b * c = 5 * (b + c) := by
    have h7' : b + c ≠ 0 := h7
    field_simp [h7'] at h₄
    linarith
  have eq3 : c * a = 7 * (c + a) := by
    have h8' : c + a ≠ 0 := h8
    field_simp [h8'] at h₅
    linarith
  have eq5 : a * b + b * c + c * a = 11 * a + 9 * b + 12 * c := by
    linarith [eq1, eq2, eq3]
  have eq9 : (a * b * c) / (a * b + b * c + c * a) = 280 / 83 := by
    have h10 : a * b + b * c + c * a ≠ 0 := by
      by_contra h
      have h11 : 11 * a + 9 * b + 12 * c = 0 := by
        linarith [eq5, h]
      nlinarith [sq_pos_of_ne_zero (show a + b ≠ 0 by exact h6), sq_pos_of_ne_zero (show b + c ≠ 0 by exact h7), sq_pos_of_ne_zero (show c + a ≠ 0 by exact h8), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
    have h11 : a * b + b * c + c * a = 11 * a + 9 * b + 12 * c := eq5
    field_simp [h10]
    nlinarith [sq_nonneg (a * b * c), sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a), sq_pos_of_ne_zero (show a + b ≠ 0 by exact h6), sq_pos_of_ne_zero (show b + c ≠ 0 by exact h7), sq_pos_of_ne_zero (show c + a ≠ 0 by exact h8), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
  exact eq9