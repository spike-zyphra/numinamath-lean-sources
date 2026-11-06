import Mathlib

theorem algebra_289197 :
  {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ | 
    ∃ r : ℝ, b = a * r ∧ c = b * r ∧ d = c * r ∧
    a + d = 20 ∧ b + c = 34 ∧ a^2 + b^2 + c^2 + d^2 = 1300} = ∅ := by
  ext ⟨a, b, c, d⟩
  simp [-one_div]
  intro r h1 h2 h3 h4 h5 h6
  have h7 : b = a * r := h1
  have h8 : c = b * r := h2
  have h9 : d = c * r := h3
  have h10 : c = a * r^2 := by
    rw [h7] at h8
    linarith
  have h11 : d = a * r^3 := by
    rw [h10] at h9
    linarith
  have h12 : a + d = 20 := h4
  rw [h11] at h12
  have h13 : b + c = 34 := h5
  rw [h7] at h13
  rw [h10] at h13
  have h14 : a^2 + b^2 + c^2 + d^2 = 1300 := h6
  rw [h7] at h14
  rw [h10] at h14
  rw [h11] at h14
  nlinarith [sq_nonneg (r ^ 2), sq_nonneg (a), sq_nonneg (a * r), sq_nonneg (a * r^2 - a), sq_nonneg (a * r^3 - a), sq_nonneg (a * (r^ 2 - r)), sq_nonneg (a * (r ^ 3 - r)), sq_nonneg (a * r * (r ^ 2 - 1))]