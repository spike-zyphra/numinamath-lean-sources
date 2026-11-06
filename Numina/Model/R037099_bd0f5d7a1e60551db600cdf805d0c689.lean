import Mathlib

open Real

theorem inequalities_124969 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c ≤ 3) :
    a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ 3 / 2 ∧
    3 / 2 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) := by
  constructor
  · -- First part: prove that $\frac{a}{1+a^2} + \frac{b}{1+b^2} + \frac{c}{1+c^2} \leq \frac{3}{2}$
    have h1 : a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ 3 / 2 := by
      have h2 : a / (1 + a ^ 2) ≤ (1 : ℝ) / 2 := by
        have h3 : a ^ 2 - 2 * a + 1 ≥ 0 := by nlinarith [sq_nonneg (a - 1)]
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      have h3 : b / (1 + b ^ 2) ≤ (1 : ℝ) / 2 := by
        have h4 : b ^ 2 - 2 * b + 1 ≥ 0 := by nlinarith [sq_nonneg (b - 1)]
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      have h4 : c / (1 + c ^ 2) ≤ (1 : ℝ) / 2 := by
        have h5 : c ^ 2 - 2 * c + 1 ≥ 0 := by nlinarith [sq_nonneg (c - 1)]
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith
      linarith [h2, h3, h4]
    exact h1
  · -- Second part: prove that $\frac{3}{2} \leq \frac{1}{1+a} + \frac{1}{1+b} + \frac{1}{1+c}$
    have h2 : 3 / 2 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) := by
      have h4 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 3 / 2 ≥ 0 := by
        have h5 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
        have h6 : (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) - 3 / 2) =
            (2 * ( (1 + b) * (1 + c) + (1 + a) * (1 + c) + (1 + a) * (1 + b) ) - 3 * ( (1 + a) * (1 + b) * (1 + c) ) ) / ( 2 * ( (1 + a) * (1 + b) * (1 + c) ) ) := by
          field_simp
          ring
        rw [h6]
        apply div_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a + b + c - 3), 
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc
        ]
        positivity
      linarith
    linarith [h2]