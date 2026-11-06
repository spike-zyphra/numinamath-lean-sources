import Mathlib

theorem number_theory_17032 :
    IsLeast {n : ℕ | 0 < n ∧ 4125 ∣ Nat.factorial n} 15 := by
  constructor
  · -- Show that 15 is indeed in the set
    constructor
    · -- Show 15 is positive
      norm_num
    · -- Show 4125 divides 15!
      native_decide
  · -- Show that for all n in the set, n ≥ 15
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction }
    <;> try { simp [Nat.factorial] at hn_div <;> all_goals omega }