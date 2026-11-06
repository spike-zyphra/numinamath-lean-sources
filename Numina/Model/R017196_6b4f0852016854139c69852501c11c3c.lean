import Mathlib

theorem number_theory_136187 :
    Set.ncard {(a, b, c) : ℕ × ℕ × ℕ | 2^a < 10000 ∧ 2^b < 10000 ∧ 2^c < 10000 ∧
      (2^a + 2^b + 2^c) ∣ (8^a + 8^b + 8^c)} = 86 := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | 2^a < 10000 ∧ 2^b < 10000 ∧ 2^c < 10000 ∧
      (2^a + 2^b + 2^c) ∣ (8^a + 8^b + 8^c)} = Finset.filter (fun s : ℕ × ℕ × ℕ => 
      2^(s.1) < 10000 ∧ 2^(s.2.1) < 10000 ∧ 2^(s.2.2) < 10000 ∧
        (2^(s.1) + 2^(s.2.1) + 2^(s.2.2)) ∣ (8^(s.1) + 8^(s.2.1) + 8^(s.2.2))
    ) (Finset.Icc (0 : ℕ) 13 ×ˢ Finset.Icc (0 : ℕ) 13 ×ˢ Finset.Icc (0 : ℕ) 13) := by
    ext ⟨a, b, c⟩
    simp
    intro h1 h2 h3 h4
    have h5 : a ≤ 13 := by
      by_contra h
      push_neg at h
      have h6 : 2^a ≥ 16384 := by
        have : a ≥ 14 := by omega
        have h7 : 2^a ≥ 2^14 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals norm_num
          all_goals omega
        norm_num at h7 ⊢
        linarith
      linarith
    have h6 : b ≤ 13 := by
      by_contra h
      push_neg at h
      have h7 : 2^b ≥ 16384 := by
        have : b ≥ 14 := by omega
        have h8 : 2^b ≥ 2^14 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals norm_num
          all_goals omega
        norm_num at h8 ⊢
        linarith
      linarith
    have h7 : c ≤ 13 := by
      by_contra h
      push_neg at h
      have h8 : 2^c ≥ 16384 := by
        have : c ≥ 14 := by omega
        have h9 : 2^c ≥ 2^14 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals norm_num
          all_goals omega
        norm_num at h9 ⊢
        linarith
      linarith
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide