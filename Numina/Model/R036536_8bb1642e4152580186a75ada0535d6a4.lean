import Mathlib

theorem algebra_528 (x y z : ℝ)(h1 : x = 2 * z ^ 2 / (1 + z ^ 2)) (h2 : y = 2 * x ^ 2 / (1 + x ^ 2))
(h3 : z = 2 * y ^ 2 / (1 + y ^ 2)) :
x = 0 ∧ y = 0 ∧ z = 0 ∨ x = 1 ∧ y = 1 ∧ z = 1 := by
  have h4 : x ≥ 0 := by
    have h_z2_nonneg : z ^ 2 ≥ 0 := sq_nonneg z
    have h1' : x = 2 * z ^ 2 / (1 + z ^ 2) := h1
    have h5 : (1 + z ^ 2 : ℝ) > 0 := by
      nlinarith [sq_nonneg z]
    have h_nonneg : x ≥ 0 := by
      rw [h1']
      apply div_nonneg
      · linarith
      · nlinarith
    linarith
  have h5 : y ≥ 0 := by
    have h_x2_nonneg : x ^ 2 ≥ 0 := sq_nonneg x
    have h2' : y = 2 * x ^ 2 / (1 + x ^ 2) := h2
    have h6 : (1 + x ^ 2 : ℝ) > 0 := by
      nlinarith [sq_nonneg x]
    have h_nonneg : y ≥ 0 := by
      rw [h2']
      apply div_nonneg
      · linarith
      · nlinarith
    linarith
  have h6 : z ≥ 0 := by
    have h_y2_nonneg : y ^ 2 ≥ 0 := sq_nonneg y
    have h3' : z = 2 * y ^ 2 / (1 + y ^ 2) := h3
    have h7 : (1 + y ^ 2 : ℝ) > 0 := by
      nlinarith [sq_nonneg y]
    have h_nonneg : z ≥ 0 := by
      rw [h3']
      apply div_nonneg
      · linarith
      · nlinarith
    linarith
  have h7 : x * (x - 1) ^ 2 = 0 := by
    have h11 : x = 2 * z ^ 2 / (1 + z ^ 2) := h1
    have h22 : y = 2 * x ^ 2 / (1 + x ^ 2) := h2
    have h33 : z = 2 * y ^ 2 / (1 + y ^ 2) := h3
    have h8 : x * (1 + z ^ 2) = 2 * z ^ 2 := by
      have h9 : 1 + z ^ 2 > 0 := by
        nlinarith [sq_nonneg z]
      field_simp [h9] at h11 ⊢
      nlinarith [h11]
    have h8' : y * (1 + x ^ 2) = 2 * x ^ 2 := by
      have h10 : 1 + x ^ 2 > 0 := by
        nlinarith [sq_nonneg x]
      field_simp [h10] at h22 ⊢
      nlinarith [h22]
    have h8'' : z * (1 + y ^ 2) = 2 * y ^ 2 := by
      have h11 : 1 + y ^ 2 > 0 := by
        nlinarith [sq_nonneg y]
      field_simp [h11] at h33 ⊢
      nlinarith [h33]
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      h8, h8', h8'', 
      sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x)]
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- We have $x = 0$
    have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by
      rw [hx0] at h2
      norm_num at h2 ⊢
      nlinarith
    have hz0 : z = 0 := by
      rw [hy0] at h3
      norm_num at h3 ⊢
      nlinarith
    left
    exact ⟨hx0, hy0, hz0⟩
  · -- We have $x - 1 = 0$, so $x = 1$
    have hx1 : x = 1 := by nlinarith
    have hy1 : y = 1 := by
      rw [hx1] at h2
      norm_num at h2 ⊢
      nlinarith
    have hz1 : z = 1 := by
      rw [hy1] at h3
      norm_num at h3 ⊢
      nlinarith
    right
    exact ⟨hx1, hy1, hz1⟩