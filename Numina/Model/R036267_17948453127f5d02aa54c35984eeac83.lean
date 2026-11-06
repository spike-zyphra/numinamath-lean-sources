import Mathlib

theorem number_theory_26012 :
    IsGreatest {n : ℕ | n + (Nat.ofDigits 10 (Nat.digits 10 n).reverse) = 1211} 952 := by
  constructor
  · -- Show 952 is in the set
    native_decide
  · -- Show that 952 is greatest
    intro n hn
    have h1 : n + (Nat.ofDigits 10 (Nat.digits 10 n).reverse) = 1211 := hn
    by_contra h
    push_neg at h
    have h2 : n > 952 := h
    have h3 : n ≥ 953 := by omega
    have h4 : n < 1212 := by 
      have h5 : Nat.ofDigits 10 (Nat.digits 10 n).reverse ≥ 0 := by 
        apply Nat.zero_le
      omega 
    interval_cases n <;> norm_num [Nat.ofDigits] at h1 h2 h3 h4 ⊢