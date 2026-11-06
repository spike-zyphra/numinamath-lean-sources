import Mathlib

theorem inequalities_601171 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.sqrt (a^4 + c^4) + Real.sqrt (a^4 + d^4) + Real.sqrt (b^4 + c^4) +
    Real.sqrt (b^4 + d^4) ≥ 2 * Real.sqrt 2 * (a * d + b * c) := by

  have h1 : ∀ x y : ℝ, x > 0 → y > 0 → Real.sqrt (x^4 + y^4) ≥ Real.sqrt 2 / 2 * (x^2 + y^2) := by
    intro x y hx hy 
    have h2 : Real.sqrt (x ^ 4 + y ^ 4) ≥ Real.sqrt 2 / 2 * (x ^ 2 + y ^ 2) := by
      have h3 : Real.sqrt (x ^ 4 + y ^ 4) ^ 2 ≥ (Real.sqrt 2 / 2 * (x ^ 2 + y ^ 2)) ^ 2 := by
        have h7 : Real.sqrt (x ^ 4 + y ^ 4) ^ 2 = x^4 + y^4 := Real.sq_sqrt (by positivity)
        have h8 : (Real.sqrt 2 / 2 * (x ^ 2 + y ^ 2)) ^ 2 = (Real.sqrt 2 / 2) ^ 2 * (x ^ 2 + y ^ 2) ^ 2 := by ring
        rw [h7, h8]
        have h9 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
          have h7 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          field_simp
          <;> nlinarith
        have h10 : (x ^ 2 + y ^ 2) ^ 2 = x^4 + y^4 + 2 * x ^ 2 * y ^ 2 := by ring
        rw [h9, h10] at *
        nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
      have h4 : 0 ≤ Real.sqrt (x ^ 4 + y ^ 4) := by positivity
      have h5 : 0 ≤ Real.sqrt 2 / 2 * (x ^ 2 + y ^ 2) := by 
        positivity
      nlinarith [h3, h4, h5]
    linarith
  
  have h2 : Real.sqrt (a^4 + c^4) ≥ Real.sqrt 2 / 2 * (a^2 + c^2) := by
    apply h1 a c ha hc
  have h3 : Real.sqrt (a^4 + d^4) ≥ Real.sqrt 2 / 2 * (a^2 + d^2) := by
    apply h1 a d ha hd
  have h4 : Real.sqrt (b^4 + c^4) ≥ Real.sqrt 2 / 2 * (b^2 + c^2) := by
    apply h1 b c hb hc
  have h5 : Real.sqrt (b^4 + d^4) ≥ Real.sqrt 2 / 2 * (b^2 + d^2) := by
    apply h1 b d hb hd

  have h6 : Real.sqrt (a^4 + c^4) + Real.sqrt (a^4 + d^4) + Real.sqrt (b^4 + c^4) +
    Real.sqrt (b^4 + d^4) ≥ Real.sqrt 2 * (a^2 + b^2 + c^2 + d^2) := by 
    linarith [h2, h3, h4, h5]

  have h7 : Real.sqrt 2 * (a^2 + b^2 + c^2 + d^2) ≥ 2 * Real.sqrt 2 * (a * d + b * c) := by 
    have h8 : a^2 + b^2 + c^2 + d^2 ≥ 2 * (a * d + b * c) := by 
      nlinarith [sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (a), sq_nonneg (c), sq_nonneg (b), sq_nonneg (d)]
    have h6 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, h8, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]

  linarith [h6, h7, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]