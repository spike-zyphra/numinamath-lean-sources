import Mathlib

theorem inequalities_307547 (a b c : ℝ) (h : a * b * c ≠ 0) :
    (a ^ 4 / (4 * a ^ 4 + b ^ 4 + c ^ 4) +
     b ^ 4 / (a ^ 4 + 4 * b ^ 4 + c ^ 4) +
     c ^ 4 / (a ^ 4 + b ^ 4 + 4 * c ^ 4)) ≤ 1 / 2 := by
  have ha1 : a ≠ 0 := by
    by_contra h1
    have h2 : a * b * c = 0 := by
      simp [h1]
    contradiction
  have hb1 : b ≠ 0 := by
    by_contra h1
    have h2 : a * b * c = 0 := by
      simp [h1]
    contradiction
  have hc1 : c ≠ 0 := by
    by_contra h1
    have h2 : a * b * c = 0 := by
      simp [h1]
    contradiction

  have h1 : a ^ 4 / (4 * a ^ 4 + b ^ 4 + c ^ 4) + b ^ 4 / (a ^ 4 + 4 * b ^ 4 + c ^ 4) + c ^ 4 / (a ^ 4 + b ^ 4 + 4 * c ^ 4) - 1 / 2 ≤ 0 := by
    have h2 : 0 < (4 * a^4 + b^4 + c^4 : ℝ) := by positivity
    have h3 : 0 < (a^4 + 4 * b^4 + c^4 : ℝ) := by positivity
    have h4 : 0 < (a^4 + b^4 + 4 * c^4 : ℝ) := by positivity
    have h5 : 0 < (4 * a^4 + b^4 + c^4 : ℝ) * (a^4 + 4 * b^4 + c^4 : ℝ) * (a^4 + b^4 + 4 * c^4 : ℝ) := by positivity

    have h6 : a ^ 4 / (4 * a ^ 4 + b ^ 4 + c ^ 4) + b ^ 4 / (a ^ 4 + 4 * b ^ 4 + c ^ 4) + c ^ 4 / (a ^ 4 + b ^ 4 + 4 * c ^ 4) - 1 / 2 =
        ( (a ^ 4 * (a^4 + 4 * b^4 + c^4) * (a^4 + b^4 + 4 * c^4) + 
          b^4 * (4 * a^4 + b^4 + c^4) * (a^4 + b^4 + 4 * c^4) + 
          c^4 * (4 * a^4 + b^4 + c^4) * (a^4 + 4 * b^4 + c^4) - 
          1 / 2 * (4 * a^4 + b^4 + c^4) * (a^4 + 4 * b^4 + c^4) * (a^4 + b^4 + 4 * c^4) ) / ( (4 * a^4 + b^4 + c^4 : ℝ) * (a^4 + 4 * b^4 + c^4 : ℝ) * (a^4 + b^4 + 4 * c^4 : ℝ) ) ) := by 
      field_simp 
      <;> ring
    rw [h6] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Prove that the numerator is nonpositive
      ring_nf 
      nlinarith [sq_nonneg (a^4 - b^4), sq_nonneg (a^4 - c^4), sq_nonneg (b^4 - c^4),
        sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
        sq_nonneg (a^2 * b^2 - a^2 * c^2), sq_nonneg (a^2 * b^2 - b^2 * c^2), sq_nonneg (a^2 * c^2 - b^2 * c^2),
        sq_nonneg (a^4 - b^4), sq_nonneg (a^4 - c^4), sq_nonneg (b^4 - c^4),
        mul_pos (show 0 < a^4 by positivity) (show 0 < b^4 by positivity),
        mul_pos (show 0 < a^4 by positivity) (show 0 < c^4 by positivity),
        mul_pos (show 0 < b^4 by positivity) (show 0 < c^4 by positivity) ]
    · -- Prove that the denominator is nonnegative
      positivity
  linarith