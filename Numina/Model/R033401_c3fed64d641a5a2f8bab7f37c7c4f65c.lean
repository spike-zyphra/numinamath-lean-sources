import Mathlib

theorem number_theory_16860 :
    IsLeast {a : ℕ | 0 < a ∧ (¬∃ x, a * x ≡ 1 [MOD 55]) ∧ (¬∃ x, a * x ≡ 1 [MOD 66])} 10 := by
  constructor
  · -- Show 10 is in the set
    constructor
    · -- Show 0 < 10
      norm_num
    constructor
    · -- Show 10 has no inverse in 55
      intro h
      rcases h with ⟨x, hx⟩
      norm_num [Nat.ModEq] at hx
      omega
    · -- Show 10 has no inverse in 66
      intro h
      rcases h with ⟨x, hx⟩
      norm_num [Nat.ModEq] at hx
      omega
  · -- Show 10 is the smallest
    intro a ha
    rcases ha with ⟨ha_pos, h4, h5⟩
    by_contra h
    push_neg at h
    have h1 : a < 10 := by omega
    have h2 : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 := by omega
    rcases h2 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- a = 1
      exfalso
      have h6 : ∃ x : ℕ, (1 : ℕ) * x ≡ 1 [MOD 55] := by
        use 1
        all_goals norm_num [Nat.ModEq]
      have h7 : ∃ x : ℕ, (1 : ℕ) * x ≡ 1 [MOD 66] := by
        use 1
        all_goals norm_num [Nat.ModEq]
      tauto
    · -- a = 2
      exfalso
      have h6 : ∃ x : ℕ, (2 : ℕ) * x ≡ 1 [MOD 55] := by
        use 28
        all_goals norm_num [Nat.ModEq]
      have h7 := h4 h6
      contradiction
    · -- a = 3
      exfalso
      have h6 : ∃ x : ℕ, (3 : ℕ) * x ≡ 1 [MOD 55] := by
        use 37
        all_goals norm_num [Nat.ModEq]
      have h7 := h4 h6
      contradiction
    · -- a = 4
      exfalso
      have h6 : ∃ x : ℕ, (4 : ℕ) * x ≡ 1 [MOD 55] := by
        use 14
        all_goals norm_num [Nat.ModEq]
      have h7 := h4 h6
      contradiction
    · -- a = 5
      exfalso
      have h6 : ∃ x : ℕ, (5 : ℕ) * x ≡ 1 [MOD 66] := by
        use 53
        all_goals norm_num [Nat.ModEq]
      have h7 := h5 h6
      contradiction
    · -- a = 6
      exfalso
      have h6 : ∃ x : ℕ, (6 : ℕ) * x ≡ 1 [MOD 55] := by
        use 46
        all_goals norm_num [Nat.ModEq]
      have h7 := h4 h6
      contradiction
    · -- a = 7
      exfalso
      have h6 : ∃ x : ℕ, (7 : ℕ) * x ≡ 1 [MOD 55] := by
        use 8
        all_goals norm_num [Nat.ModEq]
      have h7 := h4 h6
      contradiction
    · -- a = 8
      exfalso
      have h6 : ∃ x : ℕ, (8 : ℕ) * x ≡ 1 [MOD 55] := by
        use 7
        all_goals norm_num [Nat.ModEq]
      have h7 := h4 h6
      contradiction
    · -- a = 9
      exfalso
      have h6 : ∃ x : ℕ, (9 : ℕ) * x ≡ 1 [MOD 55] := by
        use 49
        all_goals norm_num [Nat.ModEq]
      have h7 := h4 h6
      contradiction