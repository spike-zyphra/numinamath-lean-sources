import Mathlib

theorem number_theory_23351 :
    {(A, B) : ℕ × ℕ | A > 0 ∧ B > 0 ∧ 7 > A ∧ 7 > B ∧ 
        Nat.ofDigits 7 [A, A, A] + Nat.ofDigits 7 [B, B, B] = Nat.ofDigits 7 [6, 6, 6]
    }.ncard = 5 := by
  have : {(A, B) : ℕ × ℕ | A > 0 ∧ B > 0 ∧ 7 > A ∧ 7 > B ∧ 
      Nat.ofDigits 7 [A, A, A] + Nat.ofDigits 7 [B, B, B] = Nat.ofDigits 7 [6, 6, 6]
    } = {(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)} := by
    ext ⟨A, B⟩
    simp [Nat.ofDigits, Finset.sum]
    constructor
    · -- Suppose (A, B) in the set, so:
      rintro ⟨ha_pos, hb_pos, h7a, h7b, heq⟩
      have h1 : A ≤ 6 := by
        omega
      have h2 : B ≤ 6 := by
        omega
      interval_cases A <;> interval_cases B <;> omega
    · -- Show pairs in the set:
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.ofDigits]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.ofDigits]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.ofDigits]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.ofDigits]
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Nat.ofDigits]
  rw [this]
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
  <;> try { tauto }