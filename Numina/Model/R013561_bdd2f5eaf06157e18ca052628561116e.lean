import Mathlib

theorem inequalities_189701 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (2 * Real.sqrt (a * b)) / (Real.sqrt a + Real.sqrt b) ≤ (a * b) ^ ((1 : ℝ) / 4) := by 
  have h1 : 0 < Real.sqrt a := by positivity
  have h2 : 0 < Real.sqrt b := by positivity
  have h3 : Real.sqrt a + Real.sqrt b > 0 := by positivity
  have h4 : (a * b) > 0 := mul_pos ha hb
  have h5 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by 
    rw [Real.sqrt_mul (by linarith)]
  have h7 : (a * b: ℝ) ^ ((1 : ℝ) / 4) = Real.sqrt (Real.sqrt (a * b)) := by
    have h8 : (a * b: ℝ) ^ ((1 : ℝ) / 4) = ((a * b: ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) := by 
      rw [← Real.rpow_mul]
      norm_num
      all_goals nlinarith
    have h9 : (a * b: ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (a * b) := by 
      rw [Real.sqrt_eq_rpow]
    have h10 : ((a * b: ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) = Real.sqrt (Real.sqrt (a * b)) := by 
      rw [h9] 
      have h11 : Real.sqrt (Real.sqrt (a * b)) = (Real.sqrt (a * b)) ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h11]
    rw [h8, h10]
  rw [h7, h5]
  have h5a : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by positivity)
  have h5b : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by positivity)
  have h7a : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := h5
  have h12 : Real.sqrt (Real.sqrt (a) * Real.sqrt (b)) ^ 2 = Real.sqrt (a) * Real.sqrt (b) := by
    rw [Real.sq_sqrt]
    positivity
  -- Now, we need prove $\frac{2 \cdot \sqrt{a}\cdot \sqrt{b}}{\sqrt{a} + \sqrt{b}} \leq \sqrt{\sqrt{a}\cdot \sqrt{b}}$.
  -- Multiply both sides with denominator: $\leq \implies \frac{2 \cdot \sqrt{a}\cdot \sqrt{b}}{\sqrt{a} + \sqrt{b}} \cdot (\sqrt{a} + \sqrt{b}) \leq (\sqrt{\sqrt{a}\cdot \sqrt{b}} + \sqrt{\sqrt{a}\cdot \sqrt{b}} ) $ 
  -- The left side is due to: $\frac{2 \cdot \sqrt{a}\cdot \sqrt{b}}{\sqrt{a} + \sqrt{b}} \cdot (\sqrt{a} + \sqrt{b}) \leq (\sqrt{\sqrt{a}\cdot \sqrt{b}} ) \cdot (\sqrt{a} + \sqrt{b}) $.
  have h9 : (2 * (Real.sqrt a * Real.sqrt b)) / (Real.sqrt a + Real.sqrt b) ≤ Real.sqrt (Real.sqrt a * Real.sqrt b) := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [h5a, h5b, Real.sqrt_nonneg (a), Real.sqrt_nonneg (b), 
      sq_nonneg (Real.sqrt a - Real.sqrt b), 
      sq_nonneg (Real.sqrt a * Real.sqrt b - (Real.sqrt a + Real.sqrt b) / 2), 
      Real.sq_sqrt (show 0 ≤ (a : ℝ) by positivity), 
      Real.sq_sqrt (show 0 ≤ (b : ℝ) by positivity), 
      Real.sq_sqrt (show 0 ≤ Real.sqrt a * Real.sqrt b by positivity), 
      mul_pos h1 h2, 
      sq_nonneg (Real.sqrt a * Real.sqrt b - (Real.sqrt a + Real.sqrt b) / 2), 
      Real.sqrt_nonneg (Real.sqrt a * Real.sqrt b)
    ]
  exact h9