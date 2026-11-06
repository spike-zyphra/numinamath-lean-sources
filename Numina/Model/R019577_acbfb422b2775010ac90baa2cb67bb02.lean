import Mathlib

open Real

theorem inequalities_599897 (a b c : ℝ) (h : a^2 + b^2 + c^2 + 2*a*b*c = 1) :
    sqrt ((a^2 + b^2)/(1 + a^2*b^2)) +
    sqrt ((b^2 + c^2)/(1 + b^2*c^2)) +
    sqrt ((c^2 + a^2)/(1 + c^2*a^2)) ≤ 3 := by

  have h1 : sqrt ((a^2 + b^2) / (1 + a^2 * b^2)) ≤ 1 := by
    have h11 : (a^2 + b^2) / (1 + a^2 * b^2) ≤ 1 := by
      have h3 : a^2 + b^2 ≤ 1 + a^2 * b^2 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (c - a * b), sq_nonneg (c + a * b), sq_nonneg (a^2 + b^2 - 1), sq_nonneg (c^2 - (a * b)^2), sq_nonneg (a * b * c - (1 - (a^2 + b^2 + c^2)) / 2), sq_nonneg (a + b + c - 2 * a * b * c)]
      have pos1 : 1 + a^2 * b^2 > 0 := by positivity
      apply (div_le_iff₀ pos1).mpr
      nlinarith
    have h111 : Real.sqrt ((a^2 + b^2) / (1 + a^2 * b^2)) ≤ Real.sqrt (1 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h12 : Real.sqrt (1 : ℝ) = (1 : ℝ) := by
      simp
    linarith [h111, h12]

  have h2 : sqrt ((b^2 + c^2) / (1 + b^2 * c^2)) ≤ 1 := by
    have h22 : (b^2 + c^2) / (1 + b^2 * c^2) ≤ 1 := by
      have h4 : b^2 + c^2 ≤ 1 + b^2 * c^2 := by
        nlinarith [sq_nonneg (b - c), sq_nonneg (b + c), sq_nonneg (a - c * b), sq_nonneg (a + c * b), sq_nonneg (b^2 + c^2 - 1), sq_nonneg (a^2 - (b * c)^2), sq_nonneg (a * b * c - (1 - (a^2 + b^2 + c^2)) / 2), sq_nonneg (a + b + c - 2 * a * b * c)]
      have pos1 : 1 + b^2 * c^2 > 0 := by positivity
      apply (div_le_iff₀ pos1).mpr
      nlinarith
    have h221 : Real.sqrt ((b^2 + c^2) / (1 + b^2 * c^2)) ≤ Real.sqrt (1 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h12 : Real.sqrt (1 : ℝ) = (1 : ℝ) := by
      simp
    linarith [h221, h12]

  have h3 : sqrt ((c^2 + a^2) / (1 + c^2 * a^2)) ≤ 1 := by
    have h33 : (c^2 + a^2) / (1 + c^2 * a^2) ≤ 1 := by
      have h5 : c^2 + a^2 ≤ 1 + c^2 * a^2 := by
        nlinarith [sq_nonneg (c - a), sq_nonneg (c + a), sq_nonneg (b - a * c), sq_nonneg (b + a * c), sq_nonneg (c^2 + a^2 - 1), sq_nonneg (b^2 - (a * c)^2), sq_nonneg (a * b * c - (1 - (a^2 + b^2 + c^2)) / 2), sq_nonneg (a + b + c - 2 * a * b * c)]
      have pos1 : 1 + c^2 * a^2 > 0 := by positivity
      apply (div_le_iff₀ pos1).mpr
      nlinarith
    have h331 : Real.sqrt ((c^2 + a^2) / (1 + c^2 * a^2)) ≤ Real.sqrt (1 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h12 : Real.sqrt (1 : ℝ) = (1 : ℝ) := by
      simp
    linarith [h331, h12]

  linarith [h1, h2, h3]