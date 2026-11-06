import Mathlib

theorem number_theory_4822
    (n : ℤ) (a : ℤ) (nodd : Odd n) (ncomp : ¬Prime n) (nah : a ^ n.natAbs ≡ a [ZMOD n] )
    : (n-a) ^ n.natAbs ≡ (n-a) [ZMOD n] := by
  have h8 : n.natAbs % 2 = 1 := by 
    obtain ⟨k, hk⟩ := nodd
    have : n = 2 * k + 1 := by linarith
    have h9 : n.natAbs = (2 * k + 1).natAbs := by
      rw [show n = 2 * k + 1 by linarith]
    have h10 : (2 * k + 1).natAbs % 2 = 1 := by
      have h11 : (2 * k + 1).natAbs % 2 = 1 := by 
        have h12 : (2 * k + 1 : ℤ) % 2 = 1 := by 
          omega 
        have : (2 * k + 1).natAbs % 2 = 1 := by
          omega 
        exact this 
      exact h11 
    omega 
  have h6 : (-1 : ℤ) ^ n.natAbs = -1 := by 
    have h8' : n.natAbs % 2 = 1 := h8 
    have h9 : (-1 : ℤ) ^ n.natAbs = -1 := by 
      have h10 : (-1 : ℤ) ^ n.natAbs = -1 := by
        have h11 : n.natAbs % 2 = 1 := h8'
        have h12 : (-1 : ℤ) ^ n.natAbs = -1 := by 
          rw [show n.natAbs = 2 * (n.natAbs / 2) + 1 by omega]
          rw [pow_add, pow_mul] 
          norm_num 
          <;> ring 
        exact h12 
      exact h10 
    exact h9
  have h7 : (n - a) ^ n.natAbs ≡ (-a) ^ n.natAbs [ZMOD n] := by
    have h5 : (n - a : ℤ) ≡ (-a : ℤ) [ZMOD n] := by 
      simp [Int.ModEq, sub_eq_add_neg, add_left_inj]
    have h6' : (n - a : ℤ) ^ n.natAbs ≡ (-a : ℤ) ^ n.natAbs [ZMOD n] := by 
      apply Int.ModEq.pow 
      exact h5 
    exact h6' 
  have h8' : (-a) ^ n.natAbs = (-1 : ℤ) ^ n.natAbs * a ^ n.natAbs := by 
    rw [show (-a : ℤ) = (-1 : ℤ) * a by ring]
    rw [mul_pow]
  have h13 : (n - a) ^ n.natAbs ≡ -1 * (a ^ n.natAbs) [ZMOD n] := by 
    have h14 : (n - a : ℤ) ^ n.natAbs ≡ (-a : ℤ) ^ n.natAbs [ZMOD n] := h7
    rw [h8'] at h14 
    have h17 : (-1 : ℤ) ^ n.natAbs = -1 := h6 
    rw [h17] at h14 
    exact h14 
  have h14 : -1 * (a ^ n.natAbs) ≡ -1 * (a) [ZMOD n] := by 
    have h15 : a ^ n.natAbs ≡ a [ZMOD n] := nah 
    have h16 : -1 * (a ^ n.natAbs) ≡ -1 * (a) [ZMOD n] := by 
      apply Int.ModEq.mul_left 
      exact h15 
    exact h16 
  have h16' : (n - a) ^ n.natAbs ≡ -1 * (a) [ZMOD n] := by 
    exact Int.ModEq.trans h13 h14 
  have h17 : (-1 * a : ℤ) ≡ (n - a) [ZMOD n] := by
    have h18 : (-1 * a : ℤ) % n = (n - a) % n := by 
      have h19 : (n - a + a) % n = 0 := by 
        have h21 : n - a + a = n := by ring 
        rw [h21] 
        simp 
      have h22 : (n - a) % n = (-a) % n := by 
        have h23 : (n - a : ℤ) ≡ (-a : ℤ) [ZMOD n] := by 
          have h26 : (n - a + a) ≡ (0 : ℤ) [ZMOD n] := by 
            simp [Int.ModEq] at *
            all_goals 
              try omega
          have h28 : (n - a : ℤ) ≡ (-a : ℤ) [ZMOD n] := by 
            have h30 : (n - a + a : ℤ) ≡ (0 : ℤ) [ZMOD n] := h26 
            have h31 : (n - a : ℤ) ≡ (n - a + a - a) [ZMOD n] := by 
              simp [Int.ModEq] 
            have h32 : (n - a + a : ℤ) - a = (n - a) := by ring 
            have h33 : (0 : ℤ) - a = (-a) := by ring 
            have h28 : ((n - a + a) - a) ≡ ((0 : ℤ) - a) [ZMOD n] := by 
              exact Int.ModEq.sub_right a h30 
            rw [h32, h33] at h28 
            exact h28 
          exact h28 
        exact h23 
      have h23' : (-1 * a) % n = (-a) % n := by
        simp [show -1 * a = -a by ring, Int.mul_emod, Int.neg_emod]
      omega 
    exact h18 
  exact Int.ModEq.trans h16' h17