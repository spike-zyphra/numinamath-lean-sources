import Mathlib

theorem algebra_195059 (x : ℝ) (hx : x ≠ 0) :
    (Real.sqrt (-x)^2 + (Real.sqrt (-x))^2) / (x^2 + (-x)^2) = 1 / 2016 ↔ x = -2016 := by
  constructor
  · -- Assume the equation holds, prove x = -2016
    intro h
    by_cases h1 : x ≤ 0
    · -- If x ≤ 0, then -x ≥ 0, so sqrt(-x) is well-defined
      have h2 : -x ≥ 0 := by linarith
      have h3 : Real.sqrt (-x) ^ 2 = -x := by
        rw [Real.sq_sqrt]
        linarith
      have h4 : Real.sqrt (-x) ^ 2 + Real.sqrt (-x) ^ 2 = -2 * x := by
        have h5 : Real.sqrt (-x) ^ 2 = -x := by
          rw [Real.sq_sqrt]
          linarith
        linarith [h5]
      have h6 : x^2 + (-x) ^ 2 = 2 * x ^ 2 := by
        nlinarith
      have h7 : (Real.sqrt (-x) ^ 2 + Real.sqrt (-x) ^ 2) / (x^2 + (-x) ^ 2) = (-2 * x) / (2 * x ^ 2) := by
        rw [h4, h6]
      have h8 : (-2 * x) / (2 * x ^ 2) = -1 / x := by
        field_simp [hx, show x ≠ 0 by assumption]
        <;> ring
      have h9 : x = -2016 := by
        rw [h7, h8] at h
        field_simp [hx] at h
        nlinarith
      exact h9
    · -- Assume x > 0
      have h10 : x > 0 := by nlinarith
      have h11 : -x < (0 : ℝ) := by nlinarith
      have h12 : Real.sqrt (-x) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith
      have h13 : Real.sqrt (-x) ^ 2 = 0 := by
        rw [h12]
        norm_num
      have h14 : Real.sqrt (-x) ^ 2 + Real.sqrt (-x) ^ 2 = (0 : ℝ) := by
        nlinarith [h13]
      have h15 : x^2 + (-x) ^ 2 = 2 * x ^ 2 := by
        nlinarith
      have h16 : (Real.sqrt (-x) ^ 2 + Real.sqrt (-x) ^ 2) / (x^2 + (-x) ^ 2) = 0 := by
        rw [h14, h15]
        field_simp [show x ≠ 0 by assumption, show x ^ 2 ≠ 0 by
          intro h'
          have : x = 0 := by
            nlinarith
          contradiction
        ]
        <;> nlinarith
      rw [h16] at h
      field_simp at h
  · -- Assume x = -2016, prove the equation
    intro h
    rw [h]
    have h18 : -(-2016 : ℝ) ≥ 0 := by norm_num
    have h19 : Real.sqrt (-(-2016 : ℝ)) ^ 2 = -(-2016 : ℝ) := by
      rw [Real.sq_sqrt]
      linarith
    have h20 : Real.sqrt (-(-2016 : ℝ)) ^ 2 + Real.sqrt (-(-2016 : ℝ)) ^ 2 = 4032 := by
      linarith [h19]
    have h21 : (-2016 : ℝ) ^ 2 + (-(-2016 : ℝ) : ℝ) ^ 2 = 2 * (2016 : ℝ) ^ 2 := by
      ring_nf
    rw [h20, h21]
    field_simp
    <;> norm_num