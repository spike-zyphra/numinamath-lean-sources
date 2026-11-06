import Mathlib

theorem number_theory_610846: {(x, y, z, n): ℕ × ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < n ∧ n ^ z < 2001 ∧
n ^ x + n ^ y = n ^ z}.encard = 9 := by 
  have h3 : {(x, y, z, n): ℕ × ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < n ∧ n ^ z < 2001 ∧
  n ^ x + n ^ y = n ^ z} = Finset.filter (fun s : ℕ × ℕ × ℕ × ℕ => 
    0 < (s.1 : ℕ) ∧ 0 < (s.2.1 : ℕ) ∧ 0 < (s.2.2.1 : ℕ) ∧ 0 < (s.2.2.2 : ℕ) ∧ 
    (s.2.2.2 : ℕ) ^ (s.2.2.1 : ℕ) < 2001 ∧ (s.2.2.2 : ℕ) ^ (s.1 : ℕ) + (s.2.2.2 : ℕ) ^ (s.2.1 : ℕ) = (s.2.2.2 : ℕ) ^ (s.2.2.1 : ℕ)
  ) (Finset.Icc (0 : ℕ) 30 ×ˢ Finset.Icc (0 : ℕ) 30 ×ˢ Finset.Icc (0 : ℕ) 30 ×ˢ Finset.Icc (0 : ℕ) 2000) := by
    ext ⟨x, y, z, n⟩
    simp
    intro hx hy hz hn h1 h2
    have h4 : n ≥ 2 := by
      by_contra h
      push_neg at h
      have : n = 1 := by 
        omega
      rw [this] at h2
      simp at h2 
    have h3 : n ≤ 2000 := by
      by_contra h
      push_neg at h
      have h5z : z ≥ 1 := by 
        by_contra hz2
        push_neg at hz2
        have h8 : z = 0 := by
          omega
        linarith [hz, h8]
      have h6 : n ^ z ≥ n ^ 1 := by
        apply Nat.pow_le_pow_of_le_right
        all_goals linarith
      have h7 : n ^ 1 = n := by 
        simp
      have h8 : n ^ z ≥ n := by 
        linarith [h6, h7]
      have h9 : n ^ z < 2001 := by 
        linarith
      have h9a : n ≥ 2001 := by
        linarith
      linarith [h8, h9, h9a]
    have h5 : x ≤ 30 := by
      by_contra h
      push_neg at h
      have h8 : n ^ x ≥ 2 ^ 30 := by
        have h10 : n ^ x ≥ 2 ^ x := by
          apply Nat.pow_le_pow_of_le_left 
          nlinarith
        have h11 : 2 ^ x ≥ 2 ^ 30 := by
          apply Nat.pow_le_pow_of_le_right 
          all_goals linarith
        linarith [h10, h11]
      have h10 : n ^ z < 2001 := by
        linarith
      have h2' : n ^ x + n ^ y = n ^ z := h2
      nlinarith [show n ^ y ≥ 0 by positivity, h8, h10, h2']
    have h6 : y ≤ 30 := by
      by_contra h
      push_neg at h
      have h8 : n ^ y ≥ 2 ^ 30 := by
        have h10 : n ^ y ≥ 2 ^ y := by
          apply Nat.pow_le_pow_of_le_left 
          nlinarith
        have h11 : 2 ^ y ≥ 2 ^ 30 := by
          apply Nat.pow_le_pow_of_le_right 
          all_goals linarith
        linarith [h10, h11]
      have h10 : n ^ z < 2001 := by
        linarith
      have h2' : n ^ x + n ^ y = n ^ z := h2
      nlinarith [show n ^ x ≥ 0 by positivity, h8, h10, h2']
    have h7 : z ≤ 30 := by
      by_contra h
      push_neg at h
      have h8 : n ^ z ≥ 2^31 := by
        have h9 : n ^ z ≥ 2 ^ z := by 
          apply Nat.pow_le_pow_of_le_left 
          nlinarith
        have h10 : 2 ^ z ≥ 2 ^ 31 := by 
          apply Nat.pow_le_pow_of_le_right 
          all_goals linarith
        have h11 : n ^ z ≥ 2^31 := by 
          linarith [h9, h10]
        linarith 
      have h10 : n ^ z < 2001 := by 
        linarith
      nlinarith 
    tauto
  rw [h3]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide