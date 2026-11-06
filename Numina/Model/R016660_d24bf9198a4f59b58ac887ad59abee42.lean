import Mathlib

theorem algebra_236979 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h₁ : x + Real.logb 10 x = 10) (h₂ : y + 10 ^ y = 10) :
    x + y = 10 := by
  have h₅ : x = (10 : ℝ) ^ (10 - x) := by
    have h₆ : Real.logb 10 x = 10 - x := by linarith 
    have h₇ : (x : ℝ) = (10 : ℝ) ^ (Real.logb 10 x : ℝ) := by
      rw [Real.rpow_logb]
      all_goals nlinarith 
    rw [show (Real.logb 10 x : ℝ) = (10 - x : ℝ) by linarith [h₆] ] at h₇ 
    linarith 
  have h₆ : (10 : ℝ) ^ (10 - x) = (10 - y : ℝ) := by
    have h₇ : (10 : ℝ) ^ (y : ℝ) = (10 - y : ℝ) := by 
      nlinarith 
    by_cases h₈ : (10 - x : ℝ) > (y : ℝ)
    · -- Assume $10 - x > y$
      have h₉ : (10 : ℝ) ^ (10 - x : ℝ) > (10 : ℝ) ^ (y : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt 
        all_goals nlinarith 
      nlinarith [h₇, h₉]
    · -- Assume not $10 - x > y$, so $10 - x \leq y$
      by_cases h₉ : (10 - x : ℝ) < (y : ℝ)
      · -- Assume $10 - x < y$
        have h₉' : (10 : ℝ) ^ (10 - x : ℝ) < (10 : ℝ) ^ (y : ℝ) := by 
          apply Real.rpow_lt_rpow_of_exponent_lt 
          all_goals nlinarith 
        nlinarith [h₇, h₉']
      · -- Assume $10 - x \geq y$, which leads to $10 - x = y$, $x + y = 10$
        have hᵢ : (10 - x : ℝ) = (y : ℝ) := by nlinarith 
        nlinarith [hᵢ]
  -- Finally from `h₅` and `h₆` we get `x + y = 10`.
  have eq1 : x + y = 10 := by 
    nlinarith [h₅, h₆, sq_nonneg (x - y), Real.rpow_pos_of_pos (by norm_num : (10 : ℝ) > 0) (10 - x)]
  linarith