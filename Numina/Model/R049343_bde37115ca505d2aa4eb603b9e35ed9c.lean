import Mathlib

def s : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_85854 :
    IsLeast {n | 0 < n ∧ s n = 20 ∧ s (n + 864) = 20} 695 := by
  constructor
  · -- Show that 695 is in the set
    refine ⟨by norm_num, ?_, ?_⟩
    · -- Show that s 695 = 20
      native_decide
    · -- Show that s (695 + 864) = 20
      native_decide
  · -- Show that 695 is the smallest
    intro n hn
    have ⟨hn_pos, hn1, hn2⟩ := hn
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num [s] at hn1 hn2 <;> all_goals omega