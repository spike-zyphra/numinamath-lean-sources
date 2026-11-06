import Mathlib

theorem algebra_16520 {x y z a b c : ℝ} (hnezero : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
    (h₀ : x / a + y / b + z / c = 3) (h₁ : a / x + b / y + c / z = 0) :
    x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + z ^ 2 / c ^ 2 = 9 := by
  rcases hnezero with ⟨ha, hb, hc, hx, hy, hz⟩
  have eq1 : a * y * z + b * x * z + c * x * y = 0 := by
    have eq2 : a / x + b / y + c / z = 0 := h₁
    field_simp [hx, hy, hz] at eq2 ⊢
    linarith [eq2]
  have eq3 : x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + z ^ 2 / c ^ 2 =
      (x / a + y / b + z / c) ^ 2 - 2 * ( (x * y * c + x * z * b + y * z * a) / (a * b * c) ) := by
    field_simp [ha, hb, hc]
    ring
  have eq4 : (x * y * c + x * z * b + y * z * a) / (a * b * c) = 0 := by
    have eq5 : x * y * c + x * z * b + y * z * a = 0 := by
      nlinarith [eq1]
    rw [eq5]
    norm_num
    <;> field_simp
  rw [eq3]
  rw [eq4]
  rw [h₀]
  all_goals norm_num