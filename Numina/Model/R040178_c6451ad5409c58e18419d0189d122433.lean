import Mathlib

open Real

theorem inequalities_222318 :
    IsLeast { t : ℝ | ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → Real.sqrt (x * y) ≤ t * (2 * x + 3 * y) } (1 / (2 * Real.sqrt 6)) := by
  constructor
  · -- Show that 1/(2 * sqrt 6) is in the set
    intro x y hx hy
    have hxy : x * y ≥ 0 := by
      positivity
    have h1 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
      rw [Real.sqrt_mul (by linarith)]
    have h2 : 0 ≤ x * y := by positivity
    have h3 : Real.sqrt (x * y) ≥ 0 := by positivity
    have h4 : 0 ≤ 2 * x + 3 * y := by nlinarith
    have h5 : Real.sqrt (x * y) ≤ (1 / (2 * Real.sqrt 6)) * (2 * x + 3 * y) := by
      have h6 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := h1
      have h7 : (Real.sqrt (x * y)) ^ 2 = x * y := by
        rw [Real.sq_sqrt (show 0 ≤ x * y by positivity)]
      have h8 : (x * y) ≤ (1 / (2 * Real.sqrt 6)) ^ 2 * (2 * x + 3 * y) ^ 2 := by
        have h9 : (1 / (2 * Real.sqrt 6)) ^ 2 = 1 / 24 := by
          field_simp
          <;> ring_nf <;> norm_num [Real.sq_sqrt]
        have h10 : (2 * x + 3 * y) ^ 2 ≥ 24 * (x * y) := by 
          nlinarith [sq_nonneg (2 * x - 3 * y)]
        have h11 : (1 / (2 * Real.sqrt 6)) ^ 2 * (2 * x + 3 * y) ^ 2 ≥ (x * y) := by
          rw [h9]
          nlinarith [sq_nonneg (2 * x - 3 * y)]
        linarith
      have h9 : Real.sqrt (x * y) ≤ (1 / (2 * Real.sqrt 6)) * (2 * x + 3 * y) := by
        have h10 : (Real.sqrt (x * y)) ^ 2 ≤ ((1 / (2 * Real.sqrt 6)) * (2 * x + 3 * y)) ^ 2 := by
          nlinarith [h7, h8]
        have h11 : (Real.sqrt (x * y)) ^ 2 = Real.sqrt (x * y) ^ 2 := by rfl
        have h12 : ((1 / (2 * Real.sqrt 6)) * (2 * x + 3 * y)) ^ 2 = ((1 / (2 * Real.sqrt 6)) * (2 * x + 3 * y)) ^ 2 := by rfl
        nlinarith [sq_nonneg (Real.sqrt (x * y) - (1 / (2 * Real.sqrt 6)) * (2 * x + 3 * y)), 
          mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg (x * y)), 
          show 0 ≤ (1 / (2 * Real.sqrt 6)) * (2 * x + 3 * y) by positivity
        ]
      linarith 
    linarith [h5]
  · -- Show minimality
    intro t ht 
    have ht5 := ht 3 2 (by norm_num) (by norm_num)
    have ht2 : Real.sqrt (3 * (2 : ℝ)) = Real.sqrt 6 := by
      norm_num
    rw [ht2] at ht5
    have ht6 : Real.sqrt 6 = Real.sqrt 6 := by rfl
    -- ht5 now is that sqrt(6) <= t*(2*3+3*2)
    -- which is sqrt(6) <= t*12
    -- rewrite this to t >= Real.sqrt 6 / 12
    have ht7 : (Real.sqrt 6 : ℝ) ≤ (t : ℝ) * (12 : ℝ) := by 
      nlinarith 
    have ht8 : Real.sqrt 6 ^ 2 = (6 : ℝ) := by
      rw [Real.sq_sqrt]
      all_goals linarith
    -- Now need to show t >= Real.sqrt 6 / 12
    -- But how to show that Real.sqrt 6 / 12 = 1/(2 Real.sqrt 6)
    -- Let's compute:
    -- Real.sqrt 6 / 12 = Real.sqrt 6 / 12
    -- 1/(2 Real.sqrt 6) = 1/(2 Real.sqrt 6)
    -- So need that Real.sqrt 6 / 12 = 1/(2 Real.sqrt 6)
    have ht9 : t ≥ (Real.sqrt 6 / 12 : ℝ) := by 
      nlinarith
    -- Now prove ht10 : t ≥ (1 / (2 * Real.sqrt 6) : ℝ)
    have ht10 : t ≥ (1 / (2 * Real.sqrt 6) : ℝ) := by 
      have h_eq : (Real.sqrt 6 / 12 : ℝ) = (1 / (2 * Real.sqrt 6) : ℝ) := by 
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num : (6 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num : (6 : ℝ) ≥ 0)]
      linarith [ht9, h_eq]
    linarith