import Mathlib
theorem algebra_607248 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x + y ^ 2 / x ≥ 2 * y ∧ (x + y ^ 2 / x = 2 * y ↔ x = y) := by

  have h1 : x + y ^ 2 / x - 2 * y ≥ 0 := by
    have h2 : x + y ^ 2 / x - 2 * y = (x ^ 2 + y ^ 2 - 2 * x * y) / x := by
      field_simp
      <;> ring
    rw [h2]
    have h3 : x ^ 2 + y ^ 2 - 2 * x * y ≥ 0 := by
      nlinarith [sq_nonneg (x - y)]
    have h4 : (x ^ 2 + y ^ 2 - 2 * x * y) / x ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals linarith
    linarith

  have h2 : x + y ^ 2 / x ≥ 2 * y := by linarith [h1]

  have h3 : x + y ^ 2 / x = 2 * y ↔ x = y := by
    constructor
    · -- Assume x + y^2/x = 2y prove x = y
      intro h_eq
      have h_eq1 : x ^ 2 + y ^ 2 - 2 * x * y = 0 := by
        have h_eq1 : x + y ^ 2 / x - 2 * y = 0 := by linarith [h_eq]
        have h_eq2 : (x ^ 2 + y ^ 2 - 2 * x * y) / x = 0 := by
          have h3 : x + y ^ 2 / x - 2 * y = (x ^ 2 + y ^ 2 - 2 * x * y) / x := by
            field_simp
            <;> ring
          rw [h3] at h_eq1
          linarith
        have h4 : x ^ 2 + y ^ 2 - 2 * x * y = 0 := by
          field_simp at h_eq2 ⊢
          <;> nlinarith
        linarith
      have h5 : (x - y) ^ 2 = 0 := by nlinarith [h_eq1, sq_nonneg (x - y)]
      have h6 : x - y = 0 := by
        apply pow_eq_zero 
        exact h5
      linarith
    · -- Assume x = y prove x + y^2/x = 2y
      intro h_eq
      rw [h_eq]
      field_simp
      <;> nlinarith

  constructor
  · exact h2
  · exact h3