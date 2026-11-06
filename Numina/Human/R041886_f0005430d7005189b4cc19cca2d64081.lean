import Mathlib

theorem number_theory_23036 :
    IsGreatest {n | n < 1000 ∧ 11 ∣ n} 990 := by
  constructor
  · -- First, we show that 990 belongs to the set
    exact ⟨by norm_num, by norm_num⟩
  · -- Then, we need to prove that any element in the set is at most 990
    intro n hn
    have h1 : n < 1000 := hn.1
    have h2 : 11 ∣ n := hn.2
    have : n ≤ 990 := by
      omega
    linarith