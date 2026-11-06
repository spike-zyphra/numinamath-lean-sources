import Mathlib

theorem number_theory_104611 (x y z : ℕ) :
    (2^x + 1) * (3^y + 4) * (4^z - 3) = 2015 ↔ (x = 2 ∧ y = 3 ∧ z = 2) ∨ (x = 6 ∧ y = 3 ∧ z = 1) := by
  constructor
  · -- Assume (2^x + 1) * (3^y + 4) * (4^z - 3) = 2015, prove (x = 2 ∧ y = 3 ∧ z = 2) ∨ (x = 6 ∧ y = 3 ∧ z = 1)
    intro h
    have h1 : (2^x + 1) * (3^y + 4) * (4^z - 3) = 2015 := h
    have h2 : x ≤ 11 := by
      by_contra h2
      push_neg at h2
      have h3 : 2^x + 1 ≥ 2^12 + 1 := by
        have h4 : x ≥ 12 := h2
        have h5 : 2^x ≥ 2^12 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h4
        omega
      norm_num at h3
      have h4 : (3^y + 4) * (4^z - 3) ≥ 1 := by
        apply Nat.mul_pos
        · -- Show that 3^y + 4 > 0
          positivity
        · -- Show that 4^z - 3 > 0
          by_contra h5
          push_neg at h5
          have h6 : z = 0 := by
            by_contra h7
            push_neg at h7
            have h8 : z ≥ 1 := by
              omega
            have h9 : 4^z ≥ 4 := by
              have h10 : z ≥ 1 := h8
              have h11 : 4^z ≥ 4^1 := by
                apply Nat.pow_le_pow_of_le_right (by norm_num) h10
              norm_num at h11 ⊢
              linarith
            omega
            all_goals omega
          subst z
          norm_num at h1
          all_goals omega
      have h5 : (2^x + 1) * (3^y + 4) * (4^z - 3) ≥ 4096 + 1 := by
        have h6 : (2^x + 1) ≥ 4096 + 1 := h3
        nlinarith [show (3^y + 4) * (4^z - 3) ≥ 1 from by nlinarith]
      linarith
    have h5 : z ≤ 6 := by
      by_contra h6
      push_neg at h6
      have h7 : 4^z - 3 ≥ 4^7 - 3 := by
        have h8 : z ≥ 7 := h6
        have h9 : 4^z ≥ 4^7 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h8
        omega
      norm_num at h7
      have h10 : (2^x + 1) * (3^y + 4) ≥ 1 := by
        apply Nat.mul_pos
        · -- Show 2^x + 1 > 0
          positivity
        · -- 3^y + 4 > 0
          positivity
      have h11 : (2^x + 1) * (3^y + 4) * (4^z - 3) ≥ 16381 := by
        nlinarith [show (2^x + 1) * (3^y + 4) ≥ 1 from by nlinarith, h7]
      linarith
    have h6 : y ≤ 7 := by
      by_contra h7
      push_neg at h7
      have h8 : 3^y + 4 ≥ 3^8 + 4 := by
        have h9 : y ≥ 8 := h7
        have h10 : 3^y ≥ 3^8 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h9
        omega
      norm_num at h8
      have h11 : (2^x + 1) * (3^y + 4) * (4^z - 3) ≥ 6561 + 4 := by
        nlinarith [show (2^x + 1) * (4^z - 3) ≥ 1 from by
          apply Nat.mul_pos
          · -- Show 2^x + 1 > 0
            positivity
          · -- Show 4^z - 3 > 0
            by_contra h12
            push_neg at h12
            have h13 : z = 0 := by
              by_contra h14
              push_neg at h14
              have h15 : z ≥ 1 := by
                omega
              have h16 : 4^z ≥ 4 := by
                have h17 : z ≥ 1 := h15
                have h18 : 4^z ≥ 4^1 := by
                  apply Nat.pow_le_pow_of_le_right (by norm_num) h17
                norm_num at h18 ⊢
                linarith
              omega
            subst z
            norm_num at h1
            all_goals omega
        , h8
        ]
      linarith
    interval_cases x <;> interval_cases y <;> interval_cases z
    <;> norm_num at h1 <;> tauto
  · -- Assume (x = 2 ∧ y = 3 ∧ z = 2) ∨ (x = 6 ∧ y = 3 ∧ z = 1), prove (2^x + 1) * (3^y + 4) * (4^z - 3) = 2015
    rintro (h | h)
    · -- Assume x = 2 ∧ y = 3 ∧ z = 2
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      all_goals norm_num
    · -- Assume x = 6 ∧ y = 3 ∧ z = 1
      rcases h with ⟨hx, hy, hz⟩
      rw [hx, hy, hz]
      all_goals norm_num