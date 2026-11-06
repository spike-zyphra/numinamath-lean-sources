import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_313828 (f : ℝ → ℝ) (m : ℝ) (hf : ∀ x > 0, f x > 0)
  (h₀ : ∀ x, f x = 9 ^ x - m * 3 ^ x + m + 1) :
  m < 2 + 2 * sqrt 2 := by 
  by_contra h
  push_neg at h
  have h1 : Real.sqrt 2 > 0 := by
    positivity
  have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  have h3 : (1 + Real.sqrt 2 : ℝ) > (1 : ℝ) := by 
    linarith [show Real.sqrt 2 > (0 : ℝ) by positivity]
  have h4 : (Real.logb (3 : ℝ) (1 + Real.sqrt 2)) > (0 : ℝ) := by 
    apply Real.logb_pos
    all_goals linarith
  -- Now apply hf at x = Real.logb 3 (1 + Real.sqrt 2)
  have h5 := hf (Real.logb (3 : ℝ) (1 + Real.sqrt 2)) (h4)
  have eq1 : f (Real.logb (3 : ℝ) (1 + Real.sqrt 2)) = 
    (9 : ℝ) ^ (Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) - m * ( (3 : ℝ ) ^ (Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) ) + m + 1 := by 
    specialize h₀ (Real.logb (3 : ℝ) (1 + Real.sqrt 2))
    simpa using h₀ 
  have eq2 : ( (3 : ℝ) ^ (Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) ) = (1 + Real.sqrt 2 : ℝ) := by
    rw [Real.rpow_logb]
    all_goals norm_num 
    all_goals linarith [h1]
  have eq3 : ( (9 : ℝ) ^ (Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) ) = (1 + Real.sqrt 2 : ℝ ) ^ 2 := by 
    calc
      ( (9 : ℝ) ^ (Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) ) 
          = ( (3 : ℝ) ^ ( (2 : ℝ) ) ) ^ (Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) := by norm_num 
      _ = ( (3 : ℝ) ^ (2 * Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) ) := by 
        rw [← Real.rpow_mul]
        ring_nf 
        all_goals linarith 
      _ = ( ( (3 : ℝ) ^ (Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) ) ^ 2 ) := by 
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf 
        all_goals linarith 
      _ = ( (1 + Real.sqrt 2 : ℝ ) ) ^ 2 := by 
        rw [eq2] 
  have eq4 : f (Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) = (4 + 2 * Real.sqrt 2 - m * Real.sqrt 2 ) := by 
    rw [eq1] 
    rw [eq3, eq2] 
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
  -- Contradiction.
  -- From h5
  -- f (logb 3 (1 + sqrt 2)) > 0
  -- From eq4
  -- f (logb 3 (1 + sqrt 2)) = 4 + 2 * sqrt 2 - m * sqrt 2.
  -- Therefore
  -- 4 + 2 * sqrt 2 - m * sqrt 2 > 0.
  -- But from h: m ≥ 2 + 2 * sqrt 2, we can show 4 + 2 * sqrt 2 - m * sqrt 2 ≤ 0.
  -- This is a contradiction.
  -- Let's complete the derivation.
  have h6 : (4 + 2 * Real.sqrt 2 - m * Real.sqrt 2 ) ≤ 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), h, mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2) ]
  linarith [ h5, eq4, h6 ]