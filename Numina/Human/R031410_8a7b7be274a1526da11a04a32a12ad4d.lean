import Mathlib

open Real Set
open scoped BigOperators

/- Example 1 Find the minimum value of the function
$$
f(x)=|x-1|+|x-2|+\cdots+|x-10|
$$

(2012, National High School Mathematics League Tianjin Preliminary Contest) -/
theorem algebra_150167 :
  IsLeast {x | ∃ a : ℝ, x = ∑ i : Fin 10, |a - (i + 1)|} 25 := by
  constructor
  · -- We will prove that 25 is in our set by providing a witness
    use 5
    norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, abs]
  · -- We will prove that 25 is a lower bound for our set
    intro x hx
    -- Extract the witness 'a' from the hypothesis
    rcases hx with ⟨a, rfl⟩
    -- Prove that the sum of absolute differences is at least 25
    have h1 : ∑ i : Fin 10, |a - (i + 1)| ≥ 25 := by
      norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      -- Prove that |a-1| + |a-10| ≥ 9 by considering all cases
      have h1 : |a - (1 : ℝ)| + |a - 10| ≥ 9 := by
        cases' abs_cases (a - 1) with h1 h1 <;> cases' abs_cases (a - 10) with h2 h2 <;> linarith
      -- Prove that |a-2| + |a-9| ≥ 7 by considering all cases
      have h2 : |a - (2 : ℝ)| + |a - 9| ≥ 7 := by
        cases' abs_cases (a - 2) with h1 h1 <;> cases' abs_cases (a - 9) with h2 h2 <;> linarith
      -- Prove that |a-3| + |a-8| ≥ 5 by considering all cases
      have h3 : |a - (3 : ℝ)| + |a - 8| ≥ 5 := by
        cases' abs_cases (a - 3) with h1 h1 <;> cases' abs_cases (a - 8) with h2 h2 <;> linarith
      -- Prove that |a-4| + |a-7| ≥ 3 by considering all cases
      have h4 : |a - (4 : ℝ)| + |a - 7| ≥ 3 := by
        cases' abs_cases (a - 4) with h1 h1 <;> cases' abs_cases (a - 7) with h2 h2 <;> linarith
      -- Prove that |a-5| + |a-6| ≥ 1 by considering all cases
      have h5 : |a - (5 : ℝ)| + |a - 6| ≥ 1 := by
        cases' abs_cases (a - 5) with h1 h1 <;> cases' abs_cases (a - 6) with h2 h2 <;> linarith
      -- Combine all inequalities to get the final result
      linarith
    -- Use the non-negativity of absolute values and the previous inequality to complete the proof
    linarith [abs_nonneg (a - 1), abs_nonneg (a - 2), abs_nonneg (a - 3), abs_nonneg (a - 4),
      abs_nonneg (a - 5), abs_nonneg (a - 6), abs_nonneg (a - 7), abs_nonneg (a - 8),
      abs_nonneg (a - 9), abs_nonneg (a - 10), h1]
