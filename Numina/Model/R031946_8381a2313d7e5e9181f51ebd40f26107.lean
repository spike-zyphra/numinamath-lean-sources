import Mathlib

theorem number_theory_242346 (x y : ℤ) :
    7 * x ^ 2 - 40 * x * y + 7 * y ^ 2 = (|x - y| + 2) ^ 3 ↔
    (x = 2 ∧ y = -2) ∨ (x = -2 ∧ y = 2) := by
  constructor
  · -- Assume 7 * x ^ 2 - 40 * x * y + 7 * y ^ 2 = (|x - y| + 2) ^ 3, prove (x = 2 ∧ y = -2) ∨ (x = -2 ∧ y = 2)
    intro h_eq
    by_cases h1 : x - y ≥ 0 
    · -- x - y ≥ 0 
      have h2 : |x - y| = x - y := by 
        rw [abs_of_nonneg]
        omega 
      rw [h2] at h_eq 
      have h3 : (x - y + 2) ^ 3 = 7 * x ^ 2 - 40 * x * y + 7 * y ^ 2 := by linarith 
      have h4 : x - y ≤ 7 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y - 4), sq_nonneg (x - 2), sq_nonneg (y + 2), sq_nonneg ((x - y) - 4), sq_nonneg (x - (y + 4))]
      have h5 : x - y ≥ -4 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y + 4), sq_nonneg (x + 2), sq_nonneg (y - 2), sq_nonneg ((x - y) + 4), sq_nonneg (x - (y - 4))]
      have h6 : x ≤ 10 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y + 2)]
      have h7 : y ≤ 10 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y + 2)]
      have h8 : x ≥ -10 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y + 2)]
      have h9 : y ≥ -10 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y + 2)]
      interval_cases x <;> try { 
        omega 
      } 
      <;> try { 
        interval_cases y <;> norm_num at h_eq <;> omega 
      }
    · -- x - y < 0
      have h2 : |x - y| = y - x := by 
        rw [abs_of_neg (show x - y < 0 by linarith)]
        all_goals omega 
      rw [h2] at h_eq 
      have h3 : (y - x + 2) ^ 3 = 7 * x ^ 2 - 40 * x * y + 7 * y ^ 2 := by linarith 
      have h4 : y - x ≤ 7 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg ((y - x) - 4), sq_nonneg (x + 2), sq_nonneg (y - 2), sq_nonneg ((y - x) - 4), sq_nonneg (y - (x + 4))]
      have h5 : y - x ≥ -4 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg ((y - x) + 4), sq_nonneg (x - 2), sq_nonneg (y + 2), sq_nonneg ((y - x) + 4), sq_nonneg (y - (x - 4))]
      have h6 : x ≤ 10 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg (y - x), sq_nonneg (x + 2), sq_nonneg (y - 2)]
      have h7 : y ≤ 10 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg (y - x), sq_nonneg (x + 2), sq_nonneg (y - 2)]
      have h8 : x ≥ -10 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg (y - x), sq_nonneg (x + 2), sq_nonneg (y - 2)]
      have h9 : y ≥ -10 := by 
        nlinarith [sq_nonneg (x + y), sq_nonneg (y - x), sq_nonneg (x + 2), sq_nonneg (y - 2)]
      interval_cases x <;> try { 
        omega 
      } 
      <;> try { 
        interval_cases y <;> norm_num at h_eq <;> omega 
      }
  · -- Assume the disjunction, prove the equation.
    rintro (h | h)
    · -- (x = 2 ∧ y = -2)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num [abs]
    · -- (x = -2 ∧ y = 2)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num [abs]