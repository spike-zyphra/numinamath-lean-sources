import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12804 {f : ℝ → ℝ}
  (hf : ∀ x, x < 2 → f x = 2^(2 - x))
  (hf' : ∀ x, x ≥ 2 → f x = logb 3 (x + 1)) :
  {m | ∃ x y, x ≠ y ∧ f x = m ∧ f y = m} = {m | 1 < m} := by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume there exist two distinct roots x, y such that f x = m and f y = m.
    rintro ⟨x, y, hxy, hx, hy⟩
    by_cases h1 : x < 2
    · -- Case 1: x < 2
      have hx1 : f x = (2 : ℝ) ^ (2 - x) := hf x h1
      rw [hx1] at hx
      by_cases h2 : y < 2
      · -- Case 1a: y < 2
        have hy1 : f y = (2 : ℝ) ^ (2 - y) := hf y h2
        rw [hy1] at hy
        have h_eq : (2 : ℝ) ^ (2 - x) = (2 : ℝ) ^ (2 - y) := by linarith
        have h_eq2 : 2 - x = 2 - y := by
          apply_fun (Real.logb (2 : ℝ)) at h_eq
          have h3 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 - x)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 - y)) := by
            linarith
          have h4 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 - x)) = (2 - x : ℝ) := by
            rw [Real.logb_rpow]
            all_goals
              norm_num
          have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 - y)) = (2 - y : ℝ) := by
            rw [Real.logb_rpow]
            all_goals
              norm_num
          rw [h4, h5] at h3
          linarith
        have h_eq3 : x = y := by linarith
        exfalso
        exact hxy (by linarith)
      · -- Case 1b: y ≥ 2
        have hy2 : f y = logb 3 (y + 1) := hf' y (by linarith)
        rw [hy2] at hy
        have h3 : (2 : ℝ) ^ (2 - x) > 1 := by
          have h4 : (2 - x : ℝ) > (0 : ℝ) := by
            linarith
          have h5 : (2 : ℝ) ^ (2 - x : ℝ) > (2 : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt
            all_goals
              linarith
          have h6 : (2 : ℝ) ^ (0 : ℝ) = 1 := by
            norm_num
          linarith
        have h9 : m > 1 := by
          linarith [show (2 : ℝ) ^ (2 - x) = m by linarith]
        linarith
    · -- Case 2: x ≥ 2
      have hx2 : f x = logb 3 (x + 1) := hf' x (by linarith)
      rw [hx2] at hx
      by_cases h2 : y < 2
      · -- Case 2a: y < 2
        have hy1 : f y = (2 : ℝ) ^ (2 - y) := hf y h2
        rw [hy1] at hy
        have h7 : logb 3 (x + 1) ≥ 1 := by
          have hx3 : x + 1 ≥ 3 := by
            linarith
          have h9 : logb 3 (x + 1) ≥ logb 3 (3 : ℝ) := by
            apply Real.logb_le_logb_of_le
            all_goals
              linarith
          have h10 : logb 3 (3 : ℝ) = 1 := by
            rw [Real.logb_self_eq_one]
            all_goals
              norm_num
          linarith [h10, h9]
        have h9 : m ≥ 1 := by
          linarith [show logb 3 (x + 1) = m by linarith, h7]
        by_contra h
        push_neg at h
        have h10 : m ≤ (1 : ℝ) := by linarith
        have h11 : m ≥ (1 : ℝ) := by
          linarith [show m ≥ (1 : ℝ) by linarith [show logb 3 (x + 1) = m by linarith, h7]]
        have h12 : m = (1 : ℝ) := by linarith
        have h13 : (2 : ℝ) ^ (2 - y) = 1 := by
          linarith [show (2 : ℝ) ^ (2 - y) = m by linarith, h12]
        have h14 : (2 - y : ℝ) = (0 : ℝ) := by
          have h15 : (2 : ℝ) ^ (2 - y : ℝ) = (1 : ℝ) := h13
          have h16 : (2 : ℝ) ^ (2 - y : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by
            rw [h15]
            norm_num
          have h17 : (2 - y : ℝ) = (0 : ℝ) := by
            apply_fun (Real.logb (2 : ℝ)) at h16
            have h18 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 - y : ℝ)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (0 : ℝ)) := by
              linarith
            have h19 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 - y : ℝ)) = (2 - y : ℝ) := by
              rw [Real.logb_rpow]
              all_goals
                norm_num
            have h20 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (0 : ℝ)) = (0 : ℝ) := by
              rw [Real.logb_rpow]
              all_goals
                norm_num
            rw [h19, h20] at h18
            linarith
          linarith
        have h18 : y = (2 : ℝ) := by linarith
        linarith
      · -- Case 2b: y ≥ 2
        have hy2 : f y = logb 3 (y + 1) := hf' y (by linarith)
        rw [hy2] at hy
        have h_eq2 : logb 3 (x + 1) = logb 3 (y + 1) := by linarith
        have h_eq3 : x + 1 = y + 1 := by
          apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr (show x + 1 > 0 by linarith)) (Set.mem_Ioi.mpr (show y + 1 > 0 by linarith)) h_eq2
        have h_eq4 : x = y := by linarith
        exfalso
        exact hxy (by linarith)
  · -- Assume 1 < m, show there exist two distinct roots
    intro hm
    have hm1 : m > 1 := hm
    have h1 : ∃ x, x < 2 ∧ f x = m := by
      use 2 - Real.logb (2 : ℝ) m
      constructor
      · -- Show x < 2
        have h4 : Real.logb (2 : ℝ) m > 0 := by
          apply Real.logb_pos
          all_goals
            linarith
        linarith
      · -- Show f x = m
        have h5 : (2 - Real.logb (2 : ℝ) m : ℝ) < (2 : ℝ) := by
          have h4 : Real.logb (2 : ℝ) m > 0 := by
            apply Real.logb_pos
            all_goals
              linarith
          linarith
        rw [hf (2 - Real.logb (2 : ℝ) m) h5]
        have h7 : (2 : ℝ) ^ (2 - (2 - Real.logb (2 : ℝ) m) : ℝ) = m := by
          have h8 : (2 : ℝ) ^ (2 - (2 - Real.logb (2 : ℝ) m) : ℝ) = (2 : ℝ) ^ (Real.logb (2 : ℝ) m : ℝ) := by
            ring_nf
          rw [h8]
          rw [Real.rpow_logb]
          all_goals
            linarith
        linarith
    have h2 : ∃ y, y ≥ 2 ∧ f y = m := by
      use (3 : ℝ) ^ m - 1
      constructor
      · -- Show y ≥ 2
        have h9 : (3 : ℝ) ^ m > (3 : ℝ) := by
          have h11 : (3 : ℝ) ^ m > (3 : ℝ) ^ (1 : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt
            all_goals
              norm_num
              all_goals linarith
          have h12 : (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) := by
            norm_num
          linarith
        linarith [show (3 : ℝ) ^ m ≥ (3 : ℝ) by linarith]
      · -- Show f y = m
        have h10 : (3 : ℝ) ^ m - 1 ≥ (2 : ℝ) := by
          have h9 : (3 : ℝ) ^ m > (3 : ℝ) := by
            have h11 : (3 : ℝ) ^ m > (3 : ℝ) ^ (1 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_lt
              all_goals
                norm_num
                all_goals linarith
            have h12 : (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) := by
              norm_num
            linarith
          linarith
        rw [hf' ((3 : ℝ) ^ m - 1) h10]
        have h11 : logb 3 (( (3 : ℝ) ^ m - 1 ) + 1) = m := by
          have h13 : ( (3 : ℝ) ^ m - 1 ) + 1 = (3 : ℝ) ^ m := by linarith
          rw [h13]
          have h14 : logb 3 ((3 : ℝ) ^ m) = m := by
            rw [Real.logb_rpow]
            all_goals
              norm_num
          linarith
        linarith
    rcases h1 with ⟨x, hx1, hx2⟩
    rcases h2 with  ⟨y, hy1, hy2⟩
    use x, y
    constructor
    · -- Show x ≠ y
      by_contra h
      have h6 : x = y := by linarith
      have h7 : x < 2 := hx1
      have h8 : y ≥ 2 := hy1
      linarith
    constructor
    · -- Show f x = m
      exact hx2
    · -- Show f y = m
      exact hy2