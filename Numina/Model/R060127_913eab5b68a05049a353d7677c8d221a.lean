import Mathlib

theorem algebra_106625 (x : ℝ) :
    x^2 + 3 * x + 6 ≠ 0 ∧ x^2 + 7 * x + 6 ≠ 0 ∧
    5 * x / (x^2 + 3 * x + 6) + 7 * x / (x^2 + 7 * x + 6) = 1 ↔
    x = 6 ∨ x = 1 ∨ x = -2 ∨ x = -3 := by
  constructor
  · -- Forward direction: if x satisfies equation then x ∈ {6,1,-2,-3}
    rintro ⟨hx₁, hx₂, heq⟩
    -- Multiply through by denominators to clear fractions:
    -- 5x*(x^2+7x+6) + 7x*(x^2+3x+6) = (x^2+3x+6)(x^2+7x+6)
    have h1 : x^2 + 3 * x + 6 ≠ 0 := hx₁
    have h2 : x^2 + 7 * x + 6 ≠ 0 := hx₂
    have eq1 : 5 * x * (x ^ 2 + 7 * x + 6) + 7 * x * (x ^ 2 + 3 * x + 6) =
          (x^2 + 3 * x + 6) * (x^2 + 7 * x + 6) := by
      have eq2 : 5 * x / (x^2 + 3 * x + 6) + 7 * x / (x^2 + 7 * x + 6) = 1 := heq
      have eq3 : 5 * x / (x^2 + 3 * x + 6) + 7 * x / (x^2 + 7 * x + 6) - 1 = 0 := by
        linarith
      have eq4 : (5 * x / (x^2 + 3 * x + 6) + 7 * x / (x^2 + 7 * x + 6) - 1) =
          ( (5 * x * (x ^ 2 + 7 * x + 6) + 7 * x * (x ^ 2 + 3 * x + 6) - (x^2 + 3 * x + 6) * (x^2 + 7 * x + 6))  ) / ( (x^2 + 3 * x + 6) * (x^2 + 7 * x + 6) ) := by
        field_simp
        <;> ring
      rw [eq4] at eq3
      have eq5 : (5 * x * (x ^ 2 + 7 * x + 6) + 7 * x * (x ^ 2 + 3 * x + 6) - (x^2 + 3 * x + 6) * (x^2 + 7 * x + 6)) / ((x^2 + 3 * x + 6) * (x^2 + 7 * x + 6)) = 0 := eq3
      have eq6 : 5 * x * (x ^ 2 + 7 * x + 6) + 7 * x * (x ^ 2 + 3 * x + 6) - (x^2 + 3 * x + 6) * (x^2 + 7 * x + 6) = 0 := by
        field_simp [(show (x^2 + 3 * x + 6) ≠ 0 by exact hx₁), 
            (show (x^2 + 7 * x + 6) ≠ 0 by exact hx₂)] at eq5 ⊢
        <;> nlinarith [eq5]
      linarith
    have eq2 : x^4 - 2*x^3 - 23*x^2 - 12*x + 36 = 0 := by
      nlinarith [eq1, sq_nonneg (x + 3), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x - 6), sq_nonneg (x^2 - 3*x - 6), sq_nonneg (x^2 +7*x +6)]
    have h3 : (x - 6) * (x + 3) * (x + 2) * (x - 1) = 0 := by
      nlinarith [eq2]
    cases' (mul_eq_zero.mp h3) with h4 h4
    cases' (mul_eq_zero.mp h4) with h4 h4
    cases' (mul_eq_zero.mp h4) with h4 h4
    · -- Case x - 6 = 0 → x = 6
      left
      linarith
    · -- Case x + 3 = 0 → x = -3
      right
      right
      right
      linarith
    · -- Case x + 2 = 0 → x = -2
      right
      right
      left
      linarith
    · -- Case x - 1 = 0 → x = 1
      right
      left
      linarith
  · -- Backward direction: each of these x satisfy the equation
    rintro (rfl | rfl | rfl | rfl)
    · constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num
    · constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num
    · constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num
    · constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num