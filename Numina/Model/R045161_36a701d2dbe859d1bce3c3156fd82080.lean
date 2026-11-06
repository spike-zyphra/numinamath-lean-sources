import Mathlib

theorem number_theory_97396 :
    IsGreatest {n | ∃ m, m < 2019 ∧ n = (Nat.digits 7 m).sum} 22 := by
  constructor
  · -- Show 22 is in the set.
    use 1714
    all_goals
      native_decide
  · -- Show that 22 is greatest.
    intro n hn
    rcases hn with ⟨m, hm1, hneq⟩
    by_contra h
    push_neg at h
    have h1 : m < 2019 := hm1
    have h2 : n = (Nat.digits 7 m).sum := by
      exact hneq
    have h3 : (Nat.digits 7 m).sum ≤ 22 := by
      have h4 : m < 2019 := by
        omega
      have h5 : (Nat.digits 7 m).sum ≤ 22 := by
        interval_cases m <;> norm_num [Nat.digits, Nat.digitsAux]
      exact h5
    have h4 : n ≤ 22 := by 
      linarith [h2, h3]
    omega