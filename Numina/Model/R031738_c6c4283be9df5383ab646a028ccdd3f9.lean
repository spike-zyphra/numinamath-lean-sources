import Mathlib

theorem algebra_229042 (a b : ℝ) (h : ∃ x : ℝ, x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0) :
    a ^ 2 + b ^ 2 ≥ 4 / 5 := by
  rcases h with ⟨x, hx⟩
  have hx1 : x ≠ 0 := by
    by_contra h1
    rw [h1] at hx
    nlinarith
  have h1 : x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0 := by linarith
  have h2 : x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by
    field_simp [hx1]
    <;> ring_nf
    <;> nlinarith
  have h3 : (x ^ 2 + 1 / x ^ 2) + a * (x + 1 / x) + b = 0 := by
    have h_eq1 : (x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1) = (x ^ 2) * ((x ^ 2 + 1 / x^2) + a * (x + 1 / x) + b) := by
      field_simp [hx1]
      <;> ring_nf
      <;> field_simp [hx1]
      <;> ring_nf
      <;> nlinarith
    rw [h_eq1] at h1
    have h6 : (x ^ 2) * ((x ^ 2 + 1 / x ^ 2) + a * (x + 1 / x) + b) = 0 := by
      nlinarith
    cases' mul_eq_zero.mp h6 with h7 h8
    · -- Case x^2 = 0 contradicts x ≠ 0
      have : x ^ 2 = 0 := by linarith
      have : x = 0 := by nlinarith
      contradiction
    · -- Case (x^2 + 1/x^2) + a*(x + 1/x) + b = 0
      nlinarith

  -- Substitute x^2 + 1/x^2
  rw [h2] at h3
  -- Let y = x + 1/x, so the equation becomes y^2 - 2 + a*y + b = 0
  -- This requires that the discriminant is non-negative
  have h5 : (x + 1 / x) ^ 2 ≥ 4 := by
    have h7 : (x + 1 / x) ^ 2 ≥ 4 := by
      have h8 : (x + 1 / x) ^ 2 - 4 ≥ 0 := by
        have h9 : (x + 1 / x) ^ 2 - 4 = (x - 1 / x) ^ 2 := by
          field_simp [hx1]
          <;> ring_nf
          <;> field_simp [hx1]
          <;> nlinarith
        rw [h9]
        positivity
      nlinarith
    nlinarith

  -- Now express b in terms of the equation
  -- From the quadratic, b = -a*(x + 1/x) - (x + 1/x)^2 + 2
  -- We need to minimize a^2 + b^2
  nlinarith [sq_nonneg (a - 4 / 5 * (x + 1 / x)), sq_nonneg (b + ( (x + 1 / x) ^ 2 ) / 5 - 2 / 5), sq_nonneg (x + 1 / x), sq_nonneg ((x + 1 / x) ^ 2 - 4), sq_nonneg ((x * (x * (x * (x * (x + 1 / x))))))
  ]