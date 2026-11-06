import Mathlib

theorem algebra_93599 (a b c : ℝ) (ha : a ≠ 0) (hc : c = b ^ 2 / (4 * a)) :
    ∀ x, a * x ^ 2 + b * x + c = 0 → x = -b / (2 * a) := by
  intro x h_eq
  rw [hc] at h_eq
  have h_eq2 : 4 * a * (a * x^2 + b * x + (b ^ 2 / (4 * a))) = 0 := by
    rw [h_eq]
    <;> norm_num
    <;> ring_nf <;> norm_num
    <;> nlinarith
  have h_eq3 : 4 * a^2 * x^2 + 4 * a * b * x + b^2 = 0 := by
    have eq2 : 4 * a * (a * x^2 + b * x + (b ^ 2 / (4 * a))) = 4 * a^2 * x^2 + 4 * a * b * x + b ^ 2 := by
      field_simp [ha]
      <;> ring
    linarith [eq2, h_eq2]
  have h_eq4 : (2 * a * x + b) ^ 2 = 0 := by
    nlinarith
  have h_eq5 : 2 * a * x + b = 0 := by
    apply pow_eq_zero 
    exact h_eq4
  have h_eq6 : x = -b / (2 * a) := by
    field_simp [ha]
    linarith [h_eq5]
  linarith [h_eq6]