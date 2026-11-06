import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_319525 {f : ℝ → ℝ}
  (hf : ∀ x, x ≤ 0 → f x = 2 ^ x)
  (hf' : ∀ x, x > 0 → f x = abs (logb 2 x)) :
  {x | f x = 1 / 2} = {-1, sqrt 2 / 2, sqrt 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume f(x) = 1/2, prove x ∈ {-1, sqrt(2)/2, sqrt(2)}
    intro h
    by_cases h1 : x ≤ 0
    · -- Case 1: x ≤ 0
      have h2 : f x = (2 : ℝ) ^ x := hf x h1
      rw [h2] at h
      have h3 : x = (-1 : ℝ) := by
        have h4 : (2 : ℝ) ^ (x : ℝ) = (1 / 2 : ℝ) := by linarith
        have h5 : x = Real.logb (2 : ℝ) (1 / 2 : ℝ) := by
          rw [← h4]
          field_simp [Real.logb_rpow]
        rw [h5]
        have h6 : Real.logb (2 : ℝ) (1 / 2 : ℝ) = -1 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        rw [h6]
      left
      exact h3
    · -- Case 2: x > 0
      have h2 : x > (0 : ℝ) := by linarith
      have h3 : f x = abs (logb 2 x) := hf' x h2
      rw [h3] at h
      have h4 : abs (logb 2 x) = (1 / 2 : ℝ) := by
        linarith
      cases' eq_or_eq_neg_of_abs_eq h4 with h5 h6
      · -- Case where logb 2 x = 1 / 2
        have h7 : logb 2 x = (1 / 2 : ℝ) := by linarith
        have h8 : x = (2 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [logb_eq_iff_rpow_eq] at h7
          · -- logb 2 x = 1/2, so x = 2^(1/2)
            linarith
          all_goals linarith
        have h9 : x = sqrt (2 : ℝ) := by
          rw [h8]
          have h10 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
          rw [h10]
        right
        right
        exact h9
      · -- Case where logb 2 x = -1 / 2
        have h7 : logb 2 x = (-1 / 2 : ℝ) := by linarith
        have h8 : x = (2 : ℝ) ^ (-1 / 2 : ℝ) := by
          rw [logb_eq_iff_rpow_eq] at h7
          · -- If log_2 x = -1/2, then x = 2^(-1/2)
            linarith
          all_goals linarith
        have h9 : x = Real.sqrt (2 : ℝ) / (2 : ℝ) := by
          rw [h8]
          have h10 : (2 : ℝ) ^ (-1 / 2 : ℝ) = Real.sqrt (2 : ℝ) / (2 : ℝ) := by
            have h11 : (2 : ℝ) ^ (-1 / 2 : ℝ) = 1 / ((2 : ℝ) ^ (1 / 2 : ℝ)) := by
              rw [show (-1 / 2 : ℝ) = - (1 / 2) by ring]
              rw [Real.rpow_neg]
              norm_num
              all_goals norm_num
            rw [h11]
            have h12 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (2 : ℝ) := by
              rw [Real.sqrt_eq_rpow]
            rw [h12]
            field_simp [Real.sqrt_ne_zero']
            <;> ring_nf <;> norm_num
          rw [h10]
        right
        left
        linarith
  · -- Assume x ∈ {-1, sqrt(2)/2, sqrt(2)}, prove f(x) = 1/2
    rintro (h | h | h)
    · -- x = -1
      rw [h]
      rw [hf (-1) (by linarith)]
      norm_num
    · -- x = sqrt(2)/2
      rw [h]
      have h1 : (sqrt (2 : ℝ) / 2 : ℝ) > 0 := by
        positivity
      rw [hf' (sqrt (2 : ℝ) / 2) h1]
      have h3 : logb 2 (sqrt (2 : ℝ) / 2) = -1 / 2 := by
        calc
          logb 2 (sqrt (2 : ℝ) / 2) = logb 2 (sqrt (2 : ℝ)) - logb 2 (2 : ℝ) := by
            rw [logb_div (by positivity) (by norm_num)]
          _ = (1 / 2 : ℝ) - (1 : ℝ) := by
            have h4 : logb (2 : ℝ) (sqrt (2 : ℝ)) = (1 / 2 : ℝ) := by
              rw [Real.sqrt_eq_rpow]
              simp [Real.logb_rpow]
            have h5 : logb (2 : ℝ) (2 : ℝ) = (1 : ℝ) := by
              norm_num [logb_eq_iff_rpow_eq]
            rw [h4, h5]
          _ = (-1 / 2 : ℝ) := by linarith
      rw [h3]
      norm_num [abs_of_neg]
    · -- x = sqrt(2)
      rw [h]
      have h1 : sqrt (2 : ℝ) > 0 := by
        positivity
      rw [hf' (sqrt (2 : ℝ)) h1]
      have h3 : logb (2 : ℝ) (sqrt (2 : ℝ)) = (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        simp [Real.logb_rpow]
      rw [h3]
      norm_num [abs_of_pos]