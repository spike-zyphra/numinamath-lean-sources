import Mathlib

theorem number_theory_628094:
    {(a, b, c) : ℕ × ℕ × ℕ | a ≤ b ∧ b ≤ c ∧ a * b * c = 2002}.encard = 14 := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a ≤ b ∧ b ≤ c ∧ a * b * c = 2002} = Finset.filter (fun s : ℕ × ℕ × ℕ => 
      (s.1 ≤ s.2.1 ∧ s.2.1 ≤ s.2.2 ∧ s.1 * s.2.1 * s.2.2 = 2002)) (Finset.Icc (0 : ℕ) 22 ×ˢ Finset.Icc (0 : ℕ) 44 ×ˢ Finset.Icc (0 : ℕ) 2002) := by
    ext ⟨a, b, c⟩
    simp
    intro h1 h2 h3
    have h4 : a ≤ 22 := by
      by_contra h
      push_neg at h
      have h5 : a * b * c > 2002 := by
        have ha1 : a ≥ 23 := by linarith
        have ha2 : b ≥ a := by linarith
        have ha3 : c ≥ b := by linarith
        have ha4 : a * b * c ≥ 23 * 23 * 23 := by
          have h1 : a ≥ 23 := ha1
          have h2 : b ≥ 23 := by linarith
          have h3 : c ≥ 23 := by linarith
          have h4 : a * b ≥ 23 * 23 := by 
            nlinarith
          nlinarith
        norm_num at ha4 ⊢
        linarith
      linarith
    have h5 : b ≤ 44 := by
      by_contra h
      push_neg at h
      have h6 : a * b * c > 2002 := by
        have hb1 : b ≥ 45 := by linarith
        have h7 : c ≥ b := by linarith
        have h8 : a ≥ 1 := by -- since a * b * c = 2002 it's non zero
          by_contra h9
          push_neg at h9
          have : a = 0 := by linarith
          rw [this] at h3
          all_goals nlinarith
        have ha2 : a * b ≥ 45 := by
          have h9 : a ≥ 1 := by linarith
          nlinarith
        nlinarith
      linarith
    -- Show c ≤ 2002.
    have h6 : c ≤ 2002 := by
      -- Since a * b * c = 2002 and a * b ≥ 1
      have h7 : a * b ≥ 1 := by
        have ha1 : a ≥ 1 := by
          by_contra h8
          push_neg at h8
          have : a = 0 := by linarith
          rw [this] at h3
          all_goals nlinarith
        have hb1 : b ≥ 1 := by
          by_contra h8
          push_neg at h8
          have : b = 0 := by linarith
          rw [this] at h3
          all_goals nlinarith
        nlinarith
        all_goals nlinarith
      nlinarith [h3, h7]
    omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide