import Mathlib

theorem algebra_195659 {x : ℝ} (hx : x ≠ 0) :
    x^3 + 1 / x^3 + x^2 + 1 / x^2 + x + 1 / x = 6 ↔ x = 1 := by
  constructor
  · -- Assume the equation holds, prove x = 1
    intro h
    have h1 : x^2 + 1 / x^2 = (x + 1 / x) ^ 2 - 2 := by
      have h2 : x^2 + 1 / x^2 = (x + 1 / x) ^ 2 - 2 * (x * (1 / x)) := by
        ring_nf
        <;> field_simp [hx] <;> ring_nf
      have h3 : x * (1 / x) = 1 := by
        field_simp [hx]
      rw [h3] at h2
      linarith
    have h3 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
      have h4 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) * (x * (1 / x)) := by
        ring_nf
        <;> field_simp [hx] <;> ring_nf
      have h5 : x * (1 / x) = 1 := by
        field_simp [hx]
      rw [h5] at h4
      linarith
    have h6 : x^3 + 1 / x^3 + x^2 + 1 / x^2 + x + 1 / x = 6 := by
      linarith
    have h7 : (x + 1 / x) ^ 3 + (x + 1 / x) ^ 2 - 2 * (x + 1 / x) - 8 = 0 := by
      have eq1 : (x + 1 / x) ^ 3 + (x + 1 / x) ^ 2 - 2 * (x + 1 / x) - 8 = 
        ((x^3 + 1 / x^3) + (x^2 + 1 / x^2) + (x + 1 / x) - 6) := by
        rw [h1, h3]
        ring_nf
        <;> field_simp [hx] <;> ring_nf
      linarith [eq1, h6]
    have h8 : (x + 1 / x - 2) * ((x + 1 / x) ^ 2 + 3 * (x + 1 / x) + 4) = 0 := by
      nlinarith [sq_nonneg ((x + 1 / x) ^ 2 + 3 * (x + 1 / x) + 4), sq_nonneg ((x + 1 / x) - 2)]
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- Case $h9 : x + 1/x - 2 = 0$
      have h9' : x + 1 / x - 2 = 0 := by
        linarith
      have h11 : (x - 1) ^ 2 = 0 := by
        field_simp [hx] at h9' 
        nlinarith
      have h12 : x - 1 = 0 := by
        apply pow_eq_zero 
        exact h11
      linarith
    · -- Case $h10 : (x + 1/x)^2 + 3(x + 1/x) + 4 = 0$
      have h21 : (x + 1 / x) ^ 2 + 3 * (x + 1 / x) + 4 = 0 := by
        linarith
      nlinarith [sq_nonneg ((x + 1 / x) + 3 / 2), sq_nonneg (x + 1 / x), sq_nonneg (x^2 + 1 / x ^ 2), sq_nonneg (x^2 - 1), sq_nonneg (x^2 - 2 * x + 1), sq_nonneg (x - 1), sq_nonneg (x + 1 / x - 2)
      ]
  · -- Assume x = 1 prove the equation
    intro h
    rw [h]
    norm_num
    <;> nlinarith