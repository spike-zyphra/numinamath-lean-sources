import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem algebra_1579
    (S : Set ℝ)
    (hS : S = {x : ℝ | x - 2 ≥ 0 ∧ √(x + 14 - 8 * √(x - 2)) + √(x + 23 - 10 * √(x - 2)) = 3}) :
    ∑ᶠ x ∈ S, x = 49 := by
  have h1 : S = {11, 38} := by 
    ext x
    simp only [hS, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x ∈ S, so x - 2 ≥ 0 and the equation
      intro h
      rcases h with ⟨hx1, heq⟩
      have h2 : x - 2 ≥ 0 := hx1
      have h3 : √(x + 14 - 8 * √(x - 2)) = abs (√(x - 2) - 4) := by
        have h4 : (x + 14 - 8 * √(x - 2) : ℝ) = (√(x - 2) - 4) ^ 2 := by
          have h5 : (√(x - 2) : ℝ) ^ 2 = x - 2 := by 
            apply Real.sq_sqrt
            linarith
          nlinarith [Real.sqrt_nonneg (x - 2), h5]
        rw [h4]
        have h5 : √((√(x - 2) - 4) ^ 2) = abs (√(x - 2) - 4) := by
          rw [Real.sqrt_sq_eq_abs]
        rw [h5]
      have h4 : √(x + 23 - 10 * √(x - 2)) = abs (√(x - 2) - 5) := by
        have h5 : (x + 23 - 10 * √(x - 2) : ℝ) = (√(x - 2) - 5) ^ 2 := by
          have h6 : (√(x - 2) : ℝ) ^ 2 = x - 2 := by
            apply Real.sq_sqrt
            linarith
          nlinarith [Real.sqrt_nonneg (x - 2), h6]
        rw [h5]
        have h7 : √((√(x - 2) - 5) ^ 2) = abs (√(x - 2) - 5) := by
          rw [Real.sqrt_sq_eq_abs]
        rw [h7]
      rw [h3, h4] at heq 
      by_cases h5 : √(x - 2) ≥ 5
      · -- Assume sqrt(x - 2) ≥ 5
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at heq
        have h6 : √(x - 2) = 6 := by
          nlinarith
        have h7 : x = 38 := by 
          have h8 : x - 2 = 36 := by
            calc
              x - 2 = (√(x - 2)) ^ 2 := by 
                rw [Real.sq_sqrt]
                linarith
              _ = 6^2 := by rw [h6]
              _ = 36 := by norm_num
          linarith
        right
        linarith
      · -- Assume sqrt(x - 2) < 5
        by_cases h6 : √(x - 2) ≥ 4
        · -- Assume 4 ≤ sqrt(x - 2) < 5
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at heq
          exfalso
          nlinarith
        · -- Assume sqrt(x - 2) < 4
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at heq
          have h6 : √(x - 2) = 3 := by
            nlinarith
          have h7 : x = 11 := by
            have h8 : x - 2 = 9 := by
              calc
                x - 2 = (√(x - 2)) ^ 2 := by 
                  rw [Real.sq_sqrt]
                  linarith
                _ = 3^2 := by rw [h6]
                _ = 9 := by norm_num
            linarith
          left
          linarith
    · -- Show that 11 and 38 are in S
      rintro (rfl | rfl)
      · -- Show 11 is in S
        constructor 
        · norm_num
        · -- Show sqrt(11 + 14 - 8 * sqrt(11 - 2)) + sqrt(11 + 23 - 10 * sqrt(11 - 2)) = 3
          have h11 : √(11 - 2) = 3 := by
            rw [Real.sqrt_eq_cases]
            all_goals norm_num
          have h1 : √(11 + 14 - 8 * √(11 - 2)) = 1 := by
            rw [h11]
            rw [Real.sqrt_eq_cases]
            all_goals norm_num
          have h2 : √(11 + 23 - 10 * √(11 - 2)) = 2 := by
            rw [h11]
            rw [Real.sqrt_eq_cases]
            all_goals norm_num
          rw [h1, h2]
          all_goals norm_num
      · -- Show 38 is in S
        constructor 
        · norm_num
        · -- Show sqrt(38 + 14 - 8 * sqrt(38 - 2)) + sqrt(38 + 23 - 10 * sqrt(38 - 2)) = 3
          have h11 : √(38 - 2) = 6 := by
            rw [Real.sqrt_eq_cases]
            all_goals norm_num
          have h1 : √(38 + 14 - 8 * √(38 - 2)) = 2 := by
            rw [h11]
            rw [Real.sqrt_eq_cases]
            all_goals norm_num
          have h2 : √(38 + 23 - 10 * √(38 - 2)) = 1 := by
            rw [h11]
            rw [Real.sqrt_eq_cases]
            all_goals norm_num
          rw [h1, h2]
          all_goals norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num