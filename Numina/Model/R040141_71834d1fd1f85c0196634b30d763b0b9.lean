import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_316108 :
  IsLeast {∑ i : Fin 10, |(x : ℝ) - (i + 1)| | x : ℝ} 25 := by
  constructor
  · -- Show that 25 is in our set
    use 5.5
    norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    all_goals norm_num [abs]
  · -- Show that 25 is the minimum element in our set
    intro y hy
    rcases hy with ⟨x, hx⟩
    -- Show that ∑ i : Fin 10, |x - (i + 1)| ≥ 25 for any x
    have hx1 : ∑ i : Fin 10, |(x : ℝ) - (i + 1)| = y := hx
    have h1 : ∑ i : Fin 10, |(x : ℝ) - (i + 1)| ≥ 25 := by
      have h2 : ∑ i : Fin 10, |(x : ℝ) - (i + 1)| = 
        (|x - (1 : ℝ)| + |x - (2 : ℝ)| + |x - (3 : ℝ)| + |x - (4 : ℝ)| + |x - (5 : ℝ)| + |x - (6 : ℝ)| + |x - (7 : ℝ)| + |x - (8 : ℝ)| + |x - (9 : ℝ)| + |x - (10 : ℝ)|) := by
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
        all_goals norm_num
        <;> ring_nf <;> norm_num
      rw [h2]
      -- Now prove that the sum is ≥ 25
      -- For each pair of terms, we can find a lower bound
      -- e.g. |x - 1| + |x - 10| ≥ 9
      --      |x - 2| + |x - 9| ≥ 7
      -- etc.
      have h3 : (|x - (1 : ℝ)| + |x - (10 : ℝ)|) ≥ 9 := by
        cases' abs_cases (x - (1 : ℝ)) with h1 h1 <;> 
          cases' abs_cases (x - (10 : ℝ)) with h2 h2 <;> 
            linarith
      have h4 : (|x - (2 : ℝ)| + |x - (9 : ℝ)|) ≥ 7 := by
        cases' abs_cases (x - (2 : ℝ)) with h1 h1 <;> 
          cases' abs_cases (x - (9 : ℝ)) with h2 h2 <;> 
            linarith
      have h5 : (|x - (3 : ℝ)| + |x - (8 : ℝ)|) ≥ 5 := by
        cases' abs_cases (x - (3 : ℝ)) with h1 h1 <;> 
          cases' abs_cases (x - (8 : ℝ)) with h2 h2 <;> 
            linarith
      have h6 : (|x - (4 : ℝ)| + |x - (7 : ℝ)|) ≥ 3 := by
        cases' abs_cases (x - (4 : ℝ)) with h1 h1 <;> 
          cases' abs_cases (x - (7 : ℝ)) with h2 h2 <;> 
            linarith
      have h7 : (|x - (5 : ℝ)| + |x - (6 : ℝ)|) ≥ 1 := by
        cases' abs_cases (x - (5 : ℝ)) with h1 h1 <;> 
          cases' abs_cases (x - (6 : ℝ)) with h2 h2 <;> 
            linarith
      linarith
    linarith [hx1, h1]