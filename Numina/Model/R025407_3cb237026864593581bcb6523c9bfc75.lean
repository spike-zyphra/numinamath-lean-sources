import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12479 :
  IsLeast {n | ∃ x : ℝ, n = ∑ i : Fin 10, |x - (i + 1)|} 25 := by
  constructor
  · -- Show 25 is achievable using x = 5.5
    use 5.5
    norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> norm_num [abs]
    <;> norm_num
  · -- Show that no value less than 25 is in the set
    intro n hn
    rcases hn with ⟨x, hx⟩
    have h1 : ∑ i : Fin 10, |x - (i + 1)| ≥ 25 := by
      have h4 : |x - (0 + 1)| + |x - (1 + 1)| + |x - (2 + 1)| + |x - (3 + 1)| + |x - (4 + 1)| +
        |x - (5 + 1)| + |x - (6 + 1)| + |x - (7 + 1)| + |x - (8 + 1)| + |x - (9 + 1)| ≥ 25 := by
        have h5 : |x - (0 + 1)| + |x - (9 + 1)| ≥ 9 := by 
          cases' abs_cases (x - (0 + 1)) with h0 h0 <;> 
            cases' abs_cases (x - (9 + 1)) with h1 h1 <;> 
              linarith
        have h6 : |x - (1 + 1)| + |x - (8 + 1)| ≥ 7 := by 
          cases' abs_cases (x - (1 + 1)) with h0 h0 <;> 
            cases' abs_cases (x - (8 + 1)) with h1 h1 <;> 
              linarith
        have h7 : |x - (2 + 1)| + |x - (7 + 1)| ≥ 5 := by 
          cases' abs_cases (x - (2 + 1)) with h0 h0 <;> 
            cases' abs_cases (x - (7 + 1)) with h1 h1 <;> 
              linarith
        have h8 : |x - (3 + 1)| + |x - (6 + 1)| ≥ 3 := by 
          cases' abs_cases (x - (3 + 1)) with h0 h0 <;> 
            cases' abs_cases (x - (6 + 1)) with h1 h1 <;> 
              linarith
        have h9 : |x - (4 + 1)| + |x - (5 + 1)| ≥ 1 := by 
          cases' abs_cases (x - (4 + 1)) with h0 h0 <;> 
            cases' abs_cases (x - (5 + 1)) with h1 h1 <;> 
              linarith
        linarith
      have h5 : ∑ i : Fin 10, |x - (i + 1)| = |x - (0 + 1)| + |x - (1 + 1)| + |x - (2 + 1)| + |x - (3 + 1)| + |x - (4 + 1)| +
        |x - (5 + 1)| + |x - (6 + 1)| + |x - (7 + 1)| + |x - (8 + 1)| + |x - (9 + 1)| := by
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
        <;> ring_nf
      linarith [h4, h5]
    linarith [h1, hx]