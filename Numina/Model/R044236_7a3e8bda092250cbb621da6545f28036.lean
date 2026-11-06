import Mathlib

theorem algebra_195143 {x y z m n p : ℝ} (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : z ≠ 0)
    (h₃ : m ≠ 0) (h₄ : n ≠ 0) (h₅ : p ≠ 0) (h₆ : x / m + y / n + z / p = 1) (h₇ : m / x + n / y + p / z = 0) :
    x ^ 2 / m ^ 2 + y ^ 2 / n ^ 2 + z ^ 2 / p ^ 2 = 1 := by 
  -- From h₇: m / x + n / y + p / z = 0 
  -- Multiply through by x * y * z to clear denominators
  have eq1 : m * y * z + n * x * z + p * x * y = 0 := by 
    have eq2 : m / x + n / y + p / z = 0 := h₇
    field_simp [h₀, h₁, h₂] at eq2 ⊢
    linarith
  
  have eq2 : x^2 / m^2 + y^2 / n^2 + z^2 / p^2 = 
      (x / m + y / n + z / p) ^ 2 - 2 * ( (x * y / (m * n)) + (x * z / (m * p)) + (y * z / (n * p)) ) := by
    field_simp [h₃, h₄, h₅]
    <;> ring
  
  have eq3 : (x * y / (m * n)) + (x * z / (m * p)) + (y * z / (n * p)) = 0 := by
    have eq1' : m * y * z + n * x * z + p * x * y = 0 := eq1
    have eq4 : (x * y / (m * n)) + (x * z / (m * p)) + (y * z / (n * p)) =
        (x * y * p + x * z * n + y * z * m) / (m * n * p) := by
      field_simp [h₃, h₄, h₅]
      <;> ring
    rw [eq4]
    have eq5 : x * y * p + x * z * n + y * z * m = 0 := by
      linarith 
    rw [eq5]
    norm_num
  
  rw [eq2, h₆, eq3]
  <;> norm_num