import Mathlib

theorem algebra_303046 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a + b + c = a * b * c) :
    ((1 - b ^ 2) * (1 - c ^ 2)) / (b * c) + ((1 - a ^ 2) * (1 - c ^ 2)) / (a * c) +
    ((1 - a ^ 2) * (1 - b ^ 2)) / (a * b) = 4 := by
  have h1 : a * b * c ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact ha
    exact hb
    exact hc
  have eq1 : ((1 - b ^ 2) * (1 - c ^ 2)) / (b * c) + ((1 - a ^ 2) * (1 - c ^ 2)) / (a * c) +
      ((1 - a ^ 2) * (1 - b ^ 2)) / (a * b) = 
      (a * (1 - b ^ 2) * (1 - c ^ 2) + b * (1 - a ^ 2) * (1 - c ^ 2) + c * (1 - a ^ 2) * (1 - b ^ 2)) / (a * b * c) := by 
    field_simp
    <;> ring
  rw [eq1]
  have eq3 : a * (1 - b ^ 2) * (1 - c ^ 2) + b * (1 - a ^ 2) * (1 - c ^ 2) + c * (1 - a ^ 2) * (1 - b ^ 2) = 4 * (a * b * c) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b * c - (a + b + c)), 
      h]
  rw [eq3]
  have eq4 : 4 * (a * b * c) / (a * b * c) = 4 := by
    have h2 : a * b * c ≠ 0 := h1
    field_simp
  simpa using eq4