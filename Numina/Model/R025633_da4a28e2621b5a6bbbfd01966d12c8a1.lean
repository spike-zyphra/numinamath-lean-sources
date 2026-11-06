import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_196556 {a : ℕ → ℝ} (ha : ∀ n, a n = sqrt (25 * n ^ 2 + 7 * n + 1) - 5 * n) :
    StrictAnti a ∧ ∀ n, a n > 0.7 := by
  constructor
  · -- Show a is strictly antitone
    intro n m h
    have h1 : n < m := by linarith
    have h2 : a n > a m := by
      rw [ha, ha]
      have h4 : (↑n : ℝ) < (↑m : ℝ) := by exact_mod_cast h
      have h4' : (5 * (↑n : ℝ)) < (5 * (↑m : ℝ)) := by nlinarith
      have h3 : sqrt (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1) - 5 * (↑n : ℝ) > sqrt (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1) - 5 * (↑m : ℝ) := by
        have h7 : sqrt (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1) > sqrt (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1) - 5 * (↑m : ℝ) + 5 * (↑n : ℝ) := by
          -- Assume that √(25n^2+7n+1) ≤ √(25m^2+7m+1) -5m+5n
          -- Then we can square both side to get a contradiction
          by_contra h
          push_neg at h
          have h8 : sqrt (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1) ≥ 5 * (↑m : ℝ) := by
            have h9 : sqrt (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) +1) ≥ sqrt ((25 * (↑m : ℝ) ^ 2)) := Real.sqrt_le_sqrt (by nlinarith)
            have h10 : sqrt (25 * (↑m : ℝ) ^ 2) = (5 * (↑m : ℝ)) := by
              have h11 : (25 * (↑m : ℝ) ^ 2 : ℝ) = (5 * (↑m : ℝ))^2 := by
                nlinarith
              rw [h11]
              rw [Real.sqrt_sq (by nlinarith)]
            nlinarith [h10]

          have h5 : sqrt (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1) ≥ 0 := by apply Real.sqrt_nonneg
          have h6 : sqrt (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1) ≥ 0 := by apply Real.sqrt_nonneg
          have h7' : sqrt (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) +1) ^ 2 ≤ (sqrt (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) +1) - 5 * (↑m : ℝ) + 5 * (↑n : ℝ)) ^ 2 := by
            nlinarith [h, Real.sqrt_nonneg (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1), 
            Real.sqrt_nonneg (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1),
            Real.sq_sqrt (show (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1 : ℝ) ≥ 0 by nlinarith),
            Real.sq_sqrt (show (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1 : ℝ) ≥ 0 by nlinarith),
            Real.sq_sqrt (show (25 * (↑m : ℝ) ^ 2) ≥ 0 by nlinarith),
            Real.sq_sqrt (show (25 * (↑n : ℝ) ^ 2) ≥ 0 by nlinarith),
            sq_nonneg (sqrt (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1) - 5 * (↑m : ℝ) + 5 * (↑n : ℝ) - sqrt (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) +1)), sq_nonneg (5 * (↑m : ℝ) - 5 * (↑n : ℝ)), sq_nonneg (sqrt (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1) - sqrt (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) +1))
            ]
          -- Substitute the sqrt square. Then we need to get a true inequality
          -- But in our case, it is a contradiction
          nlinarith [Real.sq_sqrt (show (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1 : ℝ) ≥ 0 by nlinarith), 
          Real.sq_sqrt (show (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1 : ℝ) ≥ 0 by nlinarith), 
          mul_nonneg (show 0 ≤ 5 * (↑m : ℝ) - 5 * (↑n : ℝ) by nlinarith) (show 0 ≤ 5 * (↑m : ℝ) - 5 * (↑n : ℝ) by nlinarith), sq_nonneg (sqrt (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1) - sqrt (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) +1)
          ), sq_nonneg ( (sqrt (25 * (↑m : ℝ) ^ 2 + 7 * (↑m : ℝ) + 1) - 5 * (↑m : ℝ) ) - ( sqrt (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1) - 5 * (↑n : ℝ) ) )
          ]
        nlinarith
      linarith
    linarith [h2]
  · -- Show a n >0.7
    intro n
    have hn : a n > (0.7 : ℝ) := by
      rw [ha]
      -- We need to show that sqrt(25n^2+7n+1) -5n > 0.7
      have h1 : sqrt (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1) - (5 * (↑n : ℝ)) > (0.7 : ℝ) := by
        have h4 : (5 * (↑n : ℝ) + 0.7) ^ 2 < (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1 : ℝ) := by
          ring_nf
          nlinarith
        have h5 : sqrt (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1) > (5 * (↑n : ℝ) + (0.7 : ℝ)) := by
          nlinarith [Real.sqrt_nonneg (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1), Real.sq_sqrt (show (25 * (↑n : ℝ) ^ 2 + 7 * (↑n : ℝ) + 1 : ℝ) ≥ 0 by nlinarith)]
        nlinarith
      linarith
    linarith [hn]
  all_goals try tauto