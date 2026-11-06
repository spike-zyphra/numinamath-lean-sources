import Mathlib

theorem number_theory_22821 : IsGreatest {n : ℕ | ∃ m, m > 0 ∧ m < 20 ∧ n = m.divisors.card} 6 := by
  constructor
  · -- existence, we use 12
    use 12
    all_goals native_decide
  · -- Show 6 an upper bound
    intro n hn
    rcases hn with ⟨m, hm_pos, hm_lt, hn_eq⟩
    interval_cases m <;> try { 
      norm_num [hn_eq] 
      <;> try { contradiction }
      <;> try { native_decide }
    } 
    <;> try { contradiction }