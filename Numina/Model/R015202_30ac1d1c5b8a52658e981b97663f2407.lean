import Mathlib

open Real

theorem inequalities_308651 :
    IsGreatest {x | ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a + b + c = 1 →
      a^2 + b^2 + c^2 + x * sqrt (a * b * c) ≤ 1} (2 * sqrt 3) := by
  constructor
  · -- Show that $2 \sqrt{3}$ is in the set
    intro a b c ha hb hc h1 
    have h10 : a^2 + b^2 + c^2 + (2 * Real.sqrt 3) * Real.sqrt (a * b * c) ≤ 1 := by
      have h12 : (a * b + b * c + c * a) ≥ Real.sqrt 3 * Real.sqrt (a * b * c) := by
        have h13 : 0 ≤ (a * b - b * c) ^ 2 := by nlinarith
        have h14 : 0 ≤ (b * c - c * a) ^ 2 := by nlinarith
        have h15 : 0 ≤ (c * a - a * b) ^ 2 := by nlinarith
        have h16 : (a * b + b * c + c * a) ^ 2 ≥ 3 * (a * b * c) := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
        have h17 : Real.sqrt ((a * b + b * c + c * a) ^ 2) ≥ Real.sqrt (3 * (a * b * c)) := by
          apply Real.sqrt_le_sqrt
          linarith [h16]
        have h18 : Real.sqrt ((a * b + b * c + c * a) ^ 2) = (a * b + b * c + c * a) := by
          rw [Real.sqrt_sq (show 0 ≤ a * b + b * c + c * a by positivity)]
        have h19 : Real.sqrt (3 * (a * b * c)) = Real.sqrt 3 * Real.sqrt (a * b * c) := by
          rw [Real.sqrt_mul (by positivity)]
        nlinarith [h19, h18, Real.sqrt_nonneg 3, Real.sqrt_nonneg (a * b * c)]
      have h50 : a ^ 2 + b ^ 2 + c ^ 2 = 1 - 2 * (a * b + b * c + c * a) := by
        nlinarith
      nlinarith [h50, h12, Real.sqrt_nonneg 3, Real.sqrt_nonneg (a * b * c), 
        mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg (a * b * c)), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ a * b * c by positivity), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    linarith 
  · -- Show that $2 \sqrt{3}$ is greatest in the set
    intro x hx
    have h11 : x ∈ {x | ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a + b + c = 1 →
      a^2 + b^2 + c^2 + x * sqrt (a * b * c) ≤ 1} := hx 
    have h12 := h11 (1 / 3) (1 / 3) (1 / 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h13 : (1 / 3 : ℝ) ^ 2 + (1 / 3 : ℝ) ^ 2 + (1 / 3 : ℝ) ^ 2 + x * Real.sqrt ((1 / 3) * (1 / 3) * (1 / 3)) ≤ 1 := by
      simpa using h12 
    have h14 : Real.sqrt ((1 / 3) * (1 / 3) * (1 / 3)) = Real.sqrt 3 / 9 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      <;> ring_nf <;> norm_num 
    rw [h14] at h13 
    -- Now we derive that x ≤ 2*sqrt(3)
    -- From h13: 1/3 + x*(sqrt(3)/9) <= 1 
    -- Subtract 1/3: x*(sqrt(3)/9) <= 2/3 
    -- Multiply by 9/sqrt(3): x <= (2/3)*(9/sqrt(3)) = 6/sqrt(3) = 2*sqrt(3)
    have h15 : x ≤ 2 * Real.sqrt 3 := by 
      -- From h13: 1/3 + x*(sqrt(3)/9) <= 1 
      -- Subtract 1/3: x*(sqrt(3)/9) <= 2/3 
      -- Multiply by 9/sqrt(3): x <= (2/3)*(9/sqrt(3)) = 6/sqrt(3) = 2*sqrt(3)
      have h17 : (1 / 3 : ℝ) ^ 2 + (1 / 3 : ℝ) ^ 2 + (1 / 3 : ℝ) ^ 2 + x * (Real.sqrt 3 / 9) = 1 / 3 + x * (Real.sqrt 3 / 9) := by
        ring_nf 
      have h18 : 1 / 3 + x * (Real.sqrt 3 / 9) ≤ (1 : ℝ) := by 
        nlinarith [h13, h17, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      have h19 : x * (Real.sqrt 3 / 9) ≤ 2 / 3 := by 
        nlinarith 
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    linarith