import Mathlib

theorem algebra_318233 {a b c k : ℝ} (h₀ : a * (b - c) / (b * (c - a)) = k) (h₁ : b * (c - a) / (c * (b - a)) = k)
    (h₂ : k > 0) :
    ⌊k⌋ = 0 := by
  have eq1 : b * (c - a) ≠ 0 := by
    by_contra h
    have h3 : a * (b - c) / (b * (c - a)) = 0 := by
      rw [h]
      norm_num
    linarith
  have eq2 : c * (b - a) ≠ 0 := by
    by_contra h
    have h3 : b * (c - a) / (c * (b - a)) = 0 := by
      rw [h]
      norm_num
    linarith
  have eq3 : a * (b - c) = k * (b * (c - a)) := by
    have h3 : a * (b - c) / (b * (c - a)) = k := h₀
    field_simp [eq1] at h3 ⊢
    linarith
  have eq4 : b * (c - a) = k * (c * (b - a)) := by
    have h4 : b * (c - a) / (c * (b - a)) = k := h₁
    field_simp [eq2] at h4 ⊢
    linarith
  have h3 : k ^ 2 + k - 1 = 0 := by
    apply (mul_left_inj' (show c * (b - a) ≠ 0 by exact eq2)).mp
    nlinarith [sq_pos_of_ne_zero (show b * (c - a) ≠ 0 by exact eq1), sq_pos_of_ne_zero (show c * (b - a) ≠ 0 by exact eq2),
        sq_nonneg (a * (b - c)), sq_nonneg (b * (c - a)), sq_nonneg (c * (b - a)), mul_pos h₂ (show 0 < 1 by norm_num),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (k ^ 2), sq_nonneg (k + 1 / 2), sq_nonneg (k * 2 + 1)]
  have hk1 : k < 1 := by
    nlinarith [h3, sq_nonneg (k ^ 2), sq_nonneg ((k + 1 / 2) * 2), sq_pos_of_pos h₂]
  have hk4 : ⌊k⌋ = 0 := by
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  exact hk4