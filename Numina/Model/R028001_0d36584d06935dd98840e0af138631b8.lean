import Mathlib

theorem algebra_320734 {x y z m n p : ℝ} (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : z ≠ 0)
    (h₃ : m ≠ 0) (h₄ : n ≠ 0) (h₅ : p ≠ 0) (h₆ : x / m + y / n + z / p = 1)
    (h₇ : m / x + n / y + p / z = 0) :
    x ^ 2 / m ^ 2 + y ^ 2 / n ^ 2 + z ^ 2 / p ^ 2 = 1 := by

  have h₈ : m * y * z + n * x * z + p * x * y = 0 := by
    have eq1 : m / x + n / y + p / z = 0 := h₇
    have eq2 : m / x + n / y + p / z = (m * y * z + n * x * z + p * x * y) / (x * y * z) := by
      field_simp [h₀, h₁, h₂]
      <;> ring
    rw [eq2] at eq1
    have eq3 : (m * y * z + n * x * z + p * x * y) / (x * y * z) = 0 := eq1
    have eq4 : m * y * z + n * x * z + p * x * y = 0 := by
      field_simp [show x * y * z ≠ 0 by
        apply mul_ne_zero
        apply mul_ne_zero
        exact h₀
        exact h₁
        exact h₂] at eq3 ⊢
      <;> linarith
    exact eq4

  have eq1 : x ^ 2 / m ^ 2 + y ^ 2 / n ^ 2 + z ^ 2 / p ^ 2 =
    (x / m + y / n + z / p) ^ 2 - 2 * ( (x * y) / (m * n) + (x * z) / (m * p) + (y * z) / (n * p) ) := by
    field_simp [h₃, h₄, h₅]
    <;> ring
  have eq2 : (x * y) / (m * n) + (x * z) / (m * p) + (y * z) / (n * p) = 0 := by
    have eq3 : (x * y) / (m * n) + (x * z) / (m * p) + (y * z) / (n * p) = (x * y * p + x * z * n + y * z * m) / (m * n * p) := by
      field_simp [h₃, h₄, h₅]
      <;> ring
    rw [eq3]
    have eq4 : x * y * p + x * z * n + y * z * m = 0 := by
      have h₈' : m * y * z + n * x * z + p * x * y = 0 := h₈
      linarith
    rw [eq4]
    norm_num
    <;> field_simp [h₃, h₄, h₅]

  rw [eq1, h₆, eq2]
  all_goals norm_num