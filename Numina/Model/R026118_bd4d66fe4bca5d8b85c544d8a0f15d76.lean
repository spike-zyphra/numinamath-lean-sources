import Mathlib

theorem number_theory_262619 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : Nat.factorial a * Nat.factorial b = Nat.factorial a + Nat.factorial b - Nat.factorial c) :
    (a, b) = (a, 1) ∨ (b, c) = (1, c) ∨ (a, c) = (1, 1) := by 
  by_cases h2 : b = 1
  · -- Case b = 1 
    right 
    left 
    simp [h2]
  · -- Case b >1 
    have h3 : b > 1 := by 
      by_contra h4
      push_neg at h4 
      have h5 : b = 1 := by 
        omega 
      tauto 
    by_cases h4 : a > 1 
    · -- Case a >1
      have h4_a : a ≥ 2 := by 
        omega 
      have h4_b : b ≥ 2 := by 
        omega 
      have ha1 : Nat.factorial a ≥ 2 := by 
        have h10 : a ≥ 2 := by 
          omega 
        have : Nat.factorial a ≥ Nat.factorial 2 := by 
          apply Nat.factorial_le 
          omega 
        have h20 : Nat.factorial 2 = 2 := by 
          rfl 
        linarith 
      have hb1 : Nat.factorial b ≥ 2 := by 
        have h10 : b ≥ 2 := by 
          omega 
        have : Nat.factorial b ≥ Nat.factorial 2 := by 
          apply Nat.factorial_le 
          omega 
        have h20 : Nat.factorial 2 = 2 := by 
          rfl 
        linarith 
      have h4 : Nat.factorial a * Nat.factorial b ≥ Nat.factorial a + Nat.factorial b := by 
        nlinarith [show Nat.factorial a ≥ 2 by linarith, 
          show Nat.factorial b ≥ 2 by linarith
        ]
      have h5 : Nat.factorial c ≤ 0 := by 
        omega 
      have h7 : Nat.factorial c > 0 := by 
        apply Nat.factorial_pos 
      omega 
    · -- Case a ≤ 1, thus a=1 
      have h5 : a = 1 := by 
        interval_cases a <;> omega 
      have h5a : a = 1 := h5 
      have h5b : c = 1 := by 
        rw [h5a] at h 
        have h1 : b ≥ 2 := h3 
        have hb1 : Nat.factorial b ≥ 2 := by 
          have : b ≥ 2 := h1 
          have : Nat.factorial b ≥ Nat.factorial 2 := by 
            apply Nat.factorial_le 
            omega 
          have : Nat.factorial 2 = 2 := by 
            rfl 
          linarith 
        have h_eq : 1 * Nat.factorial b = 1 + Nat.factorial b - Nat.factorial c := by
          simp [Nat.factorial] at h ⊢
          omega 
        by_cases h6 : c > 1 
        · -- Assume c ≥ 2 
          have h7 : Nat.factorial c ≥ 2 := by 
            have : c ≥ 2 := h6 
            have : Nat.factorial c ≥ Nat.factorial 2 := by 
              apply Nat.factorial_le 
              omega 
            have : Nat.factorial 2 = 2 := by 
              rfl 
            linarith 
          omega 
        · -- Assume c ≤1, so c=1 
          have h8 : c = 1 := by 
            omega 
          assumption 
      simp [h5a, h5b] 
      <;> tauto