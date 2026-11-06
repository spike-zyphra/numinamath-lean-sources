import Mathlib



theorem algebra_20899 :
    let is_emirp (n : ℕ) := Nat.Prime (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)));
    IsLeast {n | n.Prime ∧ ¬is_emirp n ∧ (Nat.digits 10 n).length = 2} 19 := by
  intro is_emirp
  constructor
  · -- Show 19 is in the set
    constructor
    · -- Show 19 is prime
      norm_num
    constructor
    · -- Show ¬is_emirp 19
      norm_num [is_emirp, Nat.ofDigits, Nat.digits, Nat.digitsAux]
    · -- Show (Nat.digits 10 19).length = 2
      norm_num
  · -- Show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨h_prime, he, h_len⟩
    by_contra h
    push_neg at h
    have h1 : n < 19 := h
    have h2 : n ≥ 10 := by
      by_contra h2
      push_neg at h2
      interval_cases n <;> norm_num at h_prime h_len
      all_goals try { contradiction }
    have h3 : n < 19 := by linarith
    interval_cases n <;> norm_num [is_emirp, Nat.ofDigits, Nat.digits, Nat.digitsAux] at he h_prime h_len
    all_goals try { contradiction }