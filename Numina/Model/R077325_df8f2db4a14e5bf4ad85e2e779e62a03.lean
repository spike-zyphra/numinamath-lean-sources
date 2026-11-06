import Mathlib

theorem number_theory_232510 :
    Set.ncard {x : ℕ | x^3 < 5000 ∧ x^3 ≡ 5 [MOD 10]} = 2 := by
  have h1 : {x : ℕ | x^3 < 5000 ∧ x^3 ≡ 5 [MOD 10]} = {5, 15} := by
    ext x
    simp [Nat.ModEq]
    constructor
    · -- Assume x^3 < 5000 and x^3 ≡ 5 [MOD 10], prove x ∈ {5, 15}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : x ≤ 17 := by
        by_contra h
        push_neg at h
        have h4 : x ≥ 18 := by
          omega
        have h5 : x ^ 3 ≥ 18 ^ 3 := by
          have h6 : x >= 18 := h4
          have h7 : x ^ 3 >= 18 ^ 3 := by
            apply Nat.pow_le_pow_of_le_left h6 3
          linarith
        norm_num at h5 ⊢
        linarith
      interval_cases x <;> norm_num at h1 h2 ⊢ <;> tauto
    · -- Assume x ∈ {5, 15}, prove x^3 < 5000 ∧ x^3 ≡ 5 [MOD 10]
      rintro (rfl | rfl)
      · constructor
        · norm_num
        · norm_num [Nat.ModEq]
      · constructor
        · norm_num
        · norm_num [Nat.ModEq]
  rw [h1]
  rw [Set.ncard_pair]
  all_goals norm_num
  all_goals try norm_num
  <;> try tauto
  <;> try omega
  <;> try trivial