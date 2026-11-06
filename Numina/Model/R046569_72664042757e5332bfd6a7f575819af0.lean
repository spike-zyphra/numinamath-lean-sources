import Mathlib

theorem number_theory_252236 :
  let nums := {n : ℕ | ∃ a b c d e : ℕ, 
    1 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧
    n = Nat.ofDigits 10 [b, a] ∧ 
    100 ≤ n^2 ∧ n^2 ≤ 999 ∧
    100 ≤ (Nat.ofDigits 10 [a, b])^2 ∧ (Nat.ofDigits 10 [a, b])^2 ≤ 999 ∧
    n^2 = Nat.ofDigits 10 [e, d, c] ∧
    (Nat.ofDigits 10 [a, b])^2 = Nat.ofDigits 10 [c, d, e]}
  nums.encard = 6 ∧ nums = {11, 12, 13, 21, 22, 31} := by

  have h1 : {n : ℕ | ∃ a b c d e : ℕ, 
    1 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧
    n = Nat.ofDigits 10 [b, a] ∧ 
    100 ≤ n^2 ∧ n^2 ≤ 999 ∧
    100 ≤ (Nat.ofDigits 10 [a, b])^2 ∧ (Nat.ofDigits 10 [a, b])^2 ≤ 999 ∧
    n^2 = Nat.ofDigits 10 [e, d, c] ∧
    (Nat.ofDigits 10 [a, b])^2 = Nat.ofDigits 10 [c, d, e]} = {11, 12, 13, 21, 22, 31} := by
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n in the set
      rintro ⟨a, b, c, d, e, ha1, ha2, hb1, hb2, hn, h1, h2, h3, h4, h5, h6⟩
      norm_num [Nat.ofDigits] at hn h5 h6 h1 h2 h3 h4
      have h31 : n ≥ 10 := by 
        nlinarith
      have h32 : n ≤ 31 := by 
        nlinarith 
      have h41 : a ≤ 3 := by 
        nlinarith 
      have h42 : b ≤ 9 := by 
        linarith 
      interval_cases a <;> interval_cases b 
      <;> omega 
    · -- Assume n ∈ {11, ..., 31}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 11
        use 1, 1, 1, 2, 1 
        all_goals norm_num [Nat.ofDigits]
      · -- n = 12
        use 1, 2, 1, 4, 4 
        all_goals norm_num [Nat.ofDigits]
      · -- n = 13
        use 1, 3, 1, 6, 9 
        all_goals norm_num [Nat.ofDigits]
      · -- n = 21 
        use 2, 1, 4, 4, 1 
        all_goals norm_num [Nat.ofDigits]
      · -- n = 22 
        use 2, 2, 4, 8, 4 
        all_goals norm_num [Nat.ofDigits]
      · -- n = 31 
        use 3, 1, 9, 6, 1 
        all_goals norm_num [Nat.ofDigits]

  rw [h1] 
  constructor
  · -- Show that the cardinality is 6 
    simp [Set.encard]
    <;> try { native_decide }
  · -- Show that the equality holds 
    tauto