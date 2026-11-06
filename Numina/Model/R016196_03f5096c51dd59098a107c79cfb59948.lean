import Mathlib

theorem algebra_303982 {x y z : ℝ} (h₀ : x + y + z = 0) (h₁ : x * y * z > 0) :
    (1 / x + 1 / y + 1 / z) < 0 := by 
  have hx1 : x ≠ 0 := by
    by_contra hx
    rw [hx] at h₁
    simp at h₁
  have hy1 : y ≠ 0 := by
    by_contra hy
    rw [hy] at h₁
    simp at h₁
  have hz1 : z ≠ 0 := by
    by_contra hz
    rw [hz] at h₁
    simp at h₁
  have h2 : 1 / x + 1 / y + 1 / z = (x * y + x * z + y * z) / (x * y * z) := by
    field_simp [hx1, hy1, hz1]
    ring
  have h3 : x * y + x * z + y * z < 0 := by
    have h4 : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + x * z + y * z) := by
      ring
    rw [show x + y + z = 0 by linarith] at h4
    have h5 : x ^ 2 + y ^ 2 + z ^ 2 > 0 := by
      have hx2 : x ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        exact hx1
      have hy2 : y ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        exact hy1
      have hz2 : z ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        exact hz1
      linarith
    nlinarith
  have h6 : (x * y + x * z + y * z) / (x * y * z) < 0 := by
    apply div_neg_of_neg_of_pos
    exact h3
    all_goals linarith
  linarith [h2, h6]