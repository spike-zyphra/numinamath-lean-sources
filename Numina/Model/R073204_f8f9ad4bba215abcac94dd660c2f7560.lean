import Mathlib

theorem number_theory_4031 :
  IsGreatest {n : ℕ | 0 < n ∧ n < 1000 ∧ (Nat.digits 10 n).sum =
    (Nat.digits 2 n).sum} 503 := by
  constructor
  · -- Show that 503 is in the set
    refine ⟨by norm_num, by norm_num, ?_⟩
    native_decide
  · -- Show that for any number n in the set, n ≤ 503
    intro n hn
    rcases hn with ⟨hn_pos, hn_lt_1000, hn_eq⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_eq <;> all_goals contradiction