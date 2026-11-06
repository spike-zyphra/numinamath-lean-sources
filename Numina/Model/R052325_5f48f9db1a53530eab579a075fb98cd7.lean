import Mathlib

theorem inequalities_599585 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a - b)^2 / (2 * (a + b)) ≤ Real.sqrt ((a^2 + b^2) / 2) - Real.sqrt (a * b) ∧
    Real.sqrt ((a^2 + b^2) / 2) - Real.sqrt (a * b) ≤ ((a - b)^2) / (4 * Real.sqrt (a * b)) := by
  constructor
  · -- First inequality: $\frac{(a-b)^{2}}{2(a+b)} \leqslant \sqrt{\frac{a^{2}+b^{2}}{2}}-\sqrt{a b}$
    have h1 : 0 < a * b := by
      nlinarith
    have h2 : Real.sqrt (a * b) > 0 := by
      positivity
    have h3 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ 0 := by
      positivity
    have h4 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b) ≥ 0 := by
      have h5 : Real.sqrt (a * b) ≤ Real.sqrt ((a^2 + b^2) / 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg (a - b)]
      linarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), Real.sqrt_nonneg (a * b), h5]
    have pos1 : 2 * (a + b) > 0 := by
      nlinarith
    have h10 : (a - b) ^ 2 / (2 * (a + b)) ≤ Real.sqrt ((a^2 + b^2) / 2) - Real.sqrt (a * b) := by
      have h7 : (a - b) ^ 2 ≤ (2 * (a + b)) * (Real.sqrt ((a^2 + b^2) / 2) - Real.sqrt (a * b)) := by
        nlinarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), Real.sqrt_nonneg (a * b), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a^2 + b^2) / 2 by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), 
          sq_nonneg (Real.sqrt ((a^2 + b^2) / 2) - Real.sqrt (a * b)), 
          sq_nonneg (a - b), 
          Real.sqrt_le_sqrt (show 0 ≤ a * b by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a * b) by positivity)]
      have pos2 : 2 * (a + b) > 0 := by
        nlinarith
      apply (div_le_iff₀ pos2).mpr
      nlinarith [h7]
      all_goals linarith
    linarith [h10]
  · -- Second inequality: $\sqrt{\frac{a^2 + b^2}{2}} - \sqrt{a b} \leq \frac{(a-b)^{2}}{4 \sqrt{a b}}$
    have h1 : 0 < a * b := by
      nlinarith
    have h2 : Real.sqrt (a * b) > 0 := by
      positivity
    have pos1 : 4 * Real.sqrt (a * b) > 0 := by
      nlinarith [Real.sqrt_pos.2 (show 0 < a * b by nlinarith)]
    have h3 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (4 * Real.sqrt (a * b)) := by
      apply (le_div_iff₀ pos1).mpr
      nlinarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), Real.sqrt_nonneg (a * b), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a^2 + b^2) / 2 by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), 
          sq_nonneg (Real.sqrt ((a^2 + b^2) / 2) - Real.sqrt (a * b)), 
          sq_nonneg (a - b), 
          Real.sqrt_le_sqrt (show 0 ≤ (a * b : ℝ) by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (a * b) by positivity)]
    linarith [h3]