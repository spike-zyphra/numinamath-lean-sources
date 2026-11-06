import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12600 {f : ℝ → ℝ}
  (hf : ∀ x, x ≤ 0 → f x = 2 ^ x)
  (hf' : ∀ x, x > 0 → f x = abs (logb 2 x)) :
  {x | f x = 1 / 2} = {-1, sqrt 2 / 2, sqrt 2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume f(x) = 1/2, prove x ∈ {-1, sqrt 2 / 2, sqrt 2}
    intro h
    by_cases h1 : x ≤ 0
    · -- If x ≤ 0, then f x = 2 ^ x
      have hfx : f x = (2 : ℝ) ^ (x : ℝ) := hf x h1
      rw [hfx] at h
      have h2 : x = -1 := by
        apply_fun (Real.logb (2 : ℝ)) at h
        simp at h
        linarith
      rw [h2]
      norm_num
    · -- Case x > 0
      have hx2 : f x = abs (logb 2 x) := hf' x (show 0 < x by linarith)
      rw [hx2] at h
      have hx2_pos : x > 0 := by linarith
      have h2 : logb 2 x = 1 / 2 ∨ logb 2 x = - (1 / 2 : ℝ) := by
        cases eq_or_eq_neg_of_abs_eq h with
        | inl h3 =>
          left
          linarith
        | inr h3 =>
          right
          linarith
      cases h2 with
      | inl h3 =>
        -- Case $\log_2 x = 1/2$
        have h4 : x = (2 : ℝ) ^ (logb 2 x : ℝ) := by
          have hx2_pos : x > 0 := by linarith
          have h5 : logb 2 x = logb 2 x := by rfl
          have h6 : (2 : ℝ) ^ (logb 2 x : ℝ) = x := by
            rw [Real.rpow_logb]
            all_goals
              try linarith
              try norm_num
          linarith
        have hx : x = (2 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [h4]
          rw [h3]
          all_goals norm_num
          all_goals linarith
        have hx5 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
        rw [hx5] at hx
        rw [hx]
        norm_num
      | inr h3 =>
        -- Case $\log_2 x = -1/2$
        have h4 : x = (2 : ℝ) ^ (logb 2 x : ℝ) := by
          have hx2_pos : x > 0 := by linarith
          have h5 : logb 2 x = logb 2 x := by rfl
          have h6 : (2 : ℝ) ^ (logb 2 x : ℝ) = x := by
            rw [Real.rpow_logb]
            all_goals
              try linarith
              try norm_num
          linarith
        have hx : x = (2 : ℝ) ^ (- (1 / 2 : ℝ)) := by
          rw [h4]
          rw [h3]
          all_goals norm_num
          all_goals linarith
        have hx6 : (2 : ℝ) ^ (- (1 / 2 : ℝ)) = Real.sqrt (2 : ℝ) / 2 := by
          have h1 : (2 : ℝ) ^ (- (1 / 2 : ℝ)) = ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
            rw [← Real.rpow_neg]
            ring_nf
            all_goals norm_num
          have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
          rw [h1, h2]
          field_simp
          <;> ring_nf <;> norm_num
        rw [hx6] at hx
        rw [hx]
        norm_num
  · -- Assume x ∈ { -1, sqrt 2 / 2, sqrt 2 }, prove f(x) = 1/2
    intro h
    rcases h with (rfl | rfl | rfl)
    · -- Case x = -1
      rw [hf (-1) (by norm_num)]
      norm_num
    · -- Case x = sqrt 2 / 2
      have h2 : sqrt (2 : ℝ) / 2 > 0 := by
        have h1 : sqrt (2 : ℝ) > 0 := by
          apply Real.sqrt_pos.mpr
          norm_num
        positivity
      rw [hf' (sqrt (2 : ℝ) / 2) h2]
      have h3 : logb 2 (sqrt (2 : ℝ) / 2) = - (1 / 2 : ℝ) := by
        calc
          logb 2 (sqrt (2 : ℝ) / 2) = logb 2 (sqrt (2 : ℝ)) - logb 2 (2 : ℝ) := by
            rw [logb_div (by positivity) (by positivity)]
          _ = (1 / 2 : ℝ) - (1 : ℝ) := by
            have h4 : logb 2 (sqrt (2 : ℝ)) = (1 / 2 : ℝ) := by
              have h5 : sqrt (2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
                rw [Real.sqrt_eq_rpow]
              rw [h5]
              simp [Real.logb_rpow]
              all_goals norm_num
            have h6 : logb 2 (2 : ℝ) = (1 : ℝ) := by
              norm_num [logb_eq_iff_rpow_eq]
            rw [h4, h6]
            all_goals norm_num
          _ = - (1 / 2 : ℝ) := by ring
      rw [h3]
      norm_num [abs_of_neg]
      <;> norm_num [abs_of_pos, abs_of_neg]
    · -- Case x = sqrt 2
      have h2 : sqrt (2 : ℝ) > 0 := by
        positivity
      rw [hf' (sqrt (2 : ℝ) ) h2]
      have h3 : logb 2 (sqrt (2 : ℝ) ) = (1 / 2 : ℝ) := by
        have h4 : sqrt (2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
        rw [h4]
        simp [Real.logb_rpow]
        all_goals norm_num
      rw [h3]
      norm_num [abs_of_pos]
      <;> norm_num [abs_of_pos, abs_of_neg]