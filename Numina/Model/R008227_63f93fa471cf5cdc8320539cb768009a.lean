import Mathlib

theorem number_theory_23136 :
    IsLeast {N : ℕ | 0 < N ∧ ¬Nat.Prime (7 + 30 * N)} 6 := by
  constructor
  · -- Show that 6 is indeed in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that 6 is the smallest
    intro N hN
    rcases hN with ⟨hN_pos, hN_not_prime⟩
    by_contra hN_lt
    push_neg at hN_lt
    interval_cases N <;> norm_num at *
    <;> try { contradiction }
    <;> try { trivial }
    <;> try { tauto }
    -- Lean will now verify each value, we have that 7 + 30 * 1 to 7 + 30 * 5 are all composite.
    -- Lean will verify all cases.
    all_goals try { contradiction }
    all_goals try { try { contradiction } <;> try { contradiction } <;> try { contradiction } }
    all_goals try { try { contradiction } <;> try { contradiction } <;> try { contradiction } }
    all_goals try { try { contradiction } <;> try { contradiction } <;> try { contradiction } }
    all_goals try { tauto }
    all_goals try { tauto }