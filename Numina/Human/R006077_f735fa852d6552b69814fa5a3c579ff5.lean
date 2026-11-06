import Mathlib
open Finset
/- find the sum of all real roots of 2 * x ^ 6 - 3* x ^ 5 + 3 * x ^ 4 + x ^ 3 - 3 * x ^ 2 + 3 * x - 1 -/

def P:= fun x: ℝ => 2 * x ^ 6 - 3* x ^ 5 + 3 * x ^ 4 + x ^ 3 - 3 * x ^ 2 + 3 * x - 1

theorem Algebra_611442: ∑ᶠ x ∈ {x: ℝ | P x = 0}, x = -1/2 := by
-- solve for the set of roots --
  have set_eq: {x: ℝ | P x = 0} = {-1 , 1/2} := by
    ext x
    constructor
    . simp
      intro a
      have eq: (x + 1) * (2 * x - 1) * (x ^ 2 - x + 1) ^ 2 = 0 := by
        calc
          (x + 1) * (2 * x - 1) * (x ^ 2 - x + 1) ^ 2 = 2 * x ^ 6 - 3* x ^ 5 + 3 * x ^ 4 + x ^ 3 - 3 * x ^ 2 + 3 * x - 1 := by ring
                                                    _ = P x := by simp [P]
                                                    _ = 0 := by exact a
      simp at eq
      rcases eq with j | k
      . rcases j with p | q
        . left
          linarith
        . right
          linarith
      . have ineq: x ^ 2 - x + 1 > 0 := by
          calc
            x ^ 2 - x + 1 = (x - 1/2) ^ 2 + 3 / 4 := by linarith
                        _ ≥ 3/4 := by simp [pow_two_nonneg]
                        _ > 0 := by linarith
        rw [k] at ineq
        linarith
    . intro a
      simp at a
      rcases a with p | q
      . rw [p]
        simp [P]
        norm_num
      . rw [q]
        simp [P]
        norm_num
  have eq: (∑ᶠ x ∈ {x: ℝ | P x = 0}, x) = (∑ x ∈ {-1 , 1/2}, x) := by
    rw [finsum_mem_eq_sum_of_inter_support_eq]
    simp
    simp [set_eq]
  rw [eq]
  norm_num