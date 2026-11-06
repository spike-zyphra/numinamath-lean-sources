import Mathlib

theorem number_theory_12852 (x : ℕ) (hx : x ≠ 0) (hsum : ∑ d in x.divisors, d = 24) (h3 : 3 ∈ x.divisors) :
    x = 15 := by
  have h4 : x ≤ 24 := by
    have h9 : x ≤ ∑ d in x.divisors, d := by
      apply Finset.single_le_sum (fun d hd => by simp) (show x ∈ x.divisors by
        simp at *
        all_goals tauto
      )
    linarith [hsum]
  interval_cases x <;> try { 
    norm_num [Finset.sum_insert, Finset.sum_singleton] at hsum h3 ⊢
    <;> try { tauto }
  }
  all_goals try { contradiction }