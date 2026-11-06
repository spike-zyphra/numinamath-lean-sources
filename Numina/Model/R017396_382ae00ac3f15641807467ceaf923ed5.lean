import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_189109 :
  IsLeast {z : ℝ | ∃ x y, z = 2015 * (x + y) / sqrt (2015 * x^2 + 2015 * y^2)} (-sqrt 4030) := by

  constructor
  · -- Show that -sqrt 4030 is in the set
    use -1, -1
    have h1 : sqrt (2015 * (-1: ℝ) ^ 2 + 2015 * (-1: ℝ) ^ 2) = Real.sqrt 4030 := by
      norm_num
    rw [h1]
    have h2 : 2015 * ((-1: ℝ) + (-1: ℝ)) / Real.sqrt 4030 = - Real.sqrt 4030 := by
      have h3 : Real.sqrt 4030 > 0 := by positivity
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 4030, Real.mul_self_sqrt (show 0 ≤ (4030: ℝ) by norm_num)]
    linarith [h2]
  · -- Show that -sqrt 4030 is the least in the set
    intro z hz
    rcases hz with ⟨x, y, hz⟩
    by_contra h
    push_neg at h
    have h4 : Real.sqrt 4030 > 0 := by positivity
    by_cases h6 : 2015 * x ^ 2 + 2015 * y ^ 2 = 0
    · -- If 2015 * x ^ 2 + 2015 * y ^ 2 = 0
      have h7 : x = 0 := by
        nlinarith
      have h8 : y = 0 := by
        nlinarith
      rw [h7, h8] at hz
      norm_num at hz ⊢
      all_goals
        nlinarith [Real.sqrt_nonneg 4030, Real.sqrt_nonneg (2015 * (0 : ℝ) ^ 2 + 2015 * (0 : ℝ) ^ 2), Real.sqrt_nonneg 4030, Real.sqrt_nonneg 0]
    · -- If 2015 * x ^ 2 + 2015 * y ^ 2 > 0
      have h7 : sqrt (2015 * x ^ 2 + 2015 * y ^ 2) > 0 := by positivity
      have h8 : -sqrt 4030 ≤ z := by
        have h9 : z = 2015 * (x + y) / sqrt (2015 * x^2 + 2015 * y^2) := hz
        have h10 : Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2) > 0 := h7
        have h11 : (Real.sqrt 4030) ^ 2 = (4030 : ℝ) := Real.sq_sqrt (by norm_num)
        have h14 : (Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2)) ^ 2 = (2015 * x^2 + 2015 * y^2 : ℝ) := Real.sq_sqrt (show 0 ≤ (2015 * x^2 + 2015 * y^2: ℝ) by positivity)
        have h15 : 2015 * (x + y) / Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2) + Real.sqrt 4030 ≥ 0 := by
          have h16 : (2015 * (x + y) / Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2) + Real.sqrt 4030) ≥ 0 := by
            have h17 : (2015 * (x + y) / Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2) + Real.sqrt 4030) * Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2) ≥ 0 := by
              have h18 : (2015 * (x + y) / Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2) + Real.sqrt 4030) * Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2) = 2015 * (x + y) + Real.sqrt 4030 * Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2) := by
                field_simp [h7]
                <;> linarith
              rw [h18]
              have h19 : 2015 * (x + y) + Real.sqrt 4030 * Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2) ≥ 0 := by
                nlinarith [sq_nonneg (2015 * (x + y) + Real.sqrt 4030 * Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2)), sq_nonneg (2015 * (x - y) - Real.sqrt 4030 * Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2)), sq_nonneg (x - y), sq_nonneg (x + y), Real.sqrt_nonneg 4030, Real.sqrt_nonneg (2015 * x ^ 2 + 2015 * y ^ 2), Real.sq_sqrt (show 0 ≤ 4030 by norm_num), Real.sq_sqrt (show 0 ≤ (2015 * x^2 + 2015 * y^2: ℝ) by positivity), mul_nonneg (Real.sqrt_nonneg 4030) (Real.sqrt_nonneg (2015 * x ^ 2 + 2015 * y ^ 2)), Real.sqrt_nonneg 4030, sq_nonneg (2015 * (x + y) - Real.sqrt 4030 * Real.sqrt (2015 * x ^ 2 + 2015 * y ^ 2)), sq_nonneg (x * y)]
              nlinarith [Real.sqrt_nonneg 4030, Real.sqrt_nonneg (2015 * x ^ 2 + 2015 * y ^ 2)]
            nlinarith [Real.sqrt_nonneg (2015 * x ^ 2 + 2015 * y ^ 2)]
          nlinarith [Real.sqrt_nonneg (2015 * x ^ 2 + 2015 * y ^ 2)]
        nlinarith [Real.sqrt_nonneg 4030, Real.sqrt_nonneg (2015 * x ^ 2 + 2015 * y ^ 2)]
      linarith [Real.sqrt_nonneg 4030, hz, h8]
      all_goals
        linarith [Real.sqrt_nonneg 4030, Real.sqrt_nonneg (2015 * x ^ 2 + 2015 * y ^ 2)]