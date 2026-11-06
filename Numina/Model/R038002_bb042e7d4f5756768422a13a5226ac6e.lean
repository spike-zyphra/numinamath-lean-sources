import Mathlib


theorem number_theory_260064 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : x * y * Nat.gcd x y = x + y + (Nat.gcd x y)^2) :
    (x, y) = (2, 2) ∨ (x, y) = (2, 3) ∨ (x, y) = (3, 2) := by

  have g1 : 0 < Nat.gcd x y := by
    have h1 : Nat.gcd x y > 0 := by
      apply Nat.gcd_pos_of_pos_left
      linarith
    linarith

  have h1 : x * y * Nat.gcd x y = x + y + (Nat.gcd x y) ^ 2 := h

  have h4 : Nat.gcd x y = 1 ∨ Nat.gcd x y = 2 := by
    by_cases h10 : Nat.gcd x y > 2
    · -- Assume that gcd(x,y) > 2, we need to show contradiction.
      have h11 : Nat.gcd x y ≥ 3 := by omega
      have h24 : x * y * Nat.gcd x y > x + y + (Nat.gcd x y) ^ 2 := by
        have h13 : Nat.gcd x y ≥ 3 := h11
        have h21 : x ≥ Nat.gcd x y := by
          have h101 : Nat.gcd x y ∣ x := by
            apply Nat.gcd_dvd_left
          rcases h101 with ⟨k, hk⟩
          have hk0 : x = Nat.gcd x y * k := by linarith
          have hk10 : k ≥ 1 := by
            by_contra h11
            push_neg at h11
            have hk00 : k = 0 := by omega
            rw [hk00] at hk0
            nlinarith
          nlinarith [show Nat.gcd x y > 0 by linarith]
        have h210 : y ≥ Nat.gcd x y := by
          have h101 : Nat.gcd x y ∣ y := by
            apply Nat.gcd_dvd_right
          rcases h101 with ⟨k, hk⟩
          have hk0 : y = Nat.gcd x y * k := by linarith
          have hk10 : k ≥ 1 := by
            by_contra h11
            push_neg at h11
            have hk00 : k = 0 := by omega
            rw [hk00] at hk0
            nlinarith
          nlinarith [show Nat.gcd x y > 0 by linarith]
        nlinarith [sq_nonneg (x - Nat.gcd x y : ℤ), sq_nonneg (y - Nat.gcd x y : ℤ),
          sq_nonneg ((x : ℤ) - (y : ℤ)), sq_nonneg ((x : ℤ) - (2 : ℤ)), sq_nonneg ((y : ℤ) - (2 : ℤ)), mul_pos (show (0 : ℤ) < x by omega) (show (0 : ℤ) < y by omega)]
      nlinarith
    · -- gcd x y ≤ 2
      have : Nat.gcd x y ≤ 2 := by
        omega
      have h16 : Nat.gcd x y = 1 ∨ Nat.gcd x y = 2 := by
        interval_cases h17 : Nat.gcd x y <;> tauto
      tauto

  rcases h4 with h4 | h4
  · -- gcd x y = 1
    have h17 : x * y = x + y + 1 := by
      rw [show Nat.gcd x y = 1 by omega] at h
      nlinarith
    have h18 : x ≤ 4 := by
      have h19 : x ≤ 4 := by
        by_contra h20
        push_neg at h20
        have h21 : y ≤ 4 := by
          nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (y - 4 : ℤ), sq_nonneg ((x : ℤ) - (y : ℤ)), sq_nonneg ((x : ℤ) - 4), sq_nonneg ((y : ℤ) - 4)]
        interval_cases y <;> omega
      omega
    have h19 : y ≤ 4 := by
      have h19 : y ≤ 4 := by
        by_contra h20
        push_neg at h20
        have h21 : x ≤ 4 := by
          nlinarith [sq_nonneg (y - 4 : ℤ), sq_nonneg (x - 4 : ℤ), sq_nonneg ((x : ℤ) - (y : ℤ)), sq_nonneg ((x : ℤ) - 4), sq_nonneg ((y : ℤ) - 4)]
        interval_cases x <;> omega
      omega
    interval_cases x <;> interval_cases y
    <;> norm_num [Prod.ext_iff] at h17 ⊢
    <;> tauto
  · -- gcd x y = 2
    have h17 : x * y * 2 = x + y + 4 := by
      rw [show Nat.gcd x y = 2 by omega] at h
      nlinarith
    have h18 : x ≤ 6 := by
      have h19 : x ≤ 6 := by
        by_contra h20
        push_neg at h20
        have h21 : y ≤ 3 := by
          nlinarith [sq_nonneg (x - 3 : ℤ), sq_nonneg (y - 3 : ℤ), sq_nonneg ((x : ℤ) - (y : ℤ)), sq_nonneg ((x : ℤ) - 3), sq_nonneg ((y : ℤ) - 3)]
        interval_cases y <;> omega
      omega
    have h19 : y ≤ 6 := by
      have h19 : y ≤ 6 := by
        by_contra h20
        push_neg at h20
        have h21 : x ≤ 3 := by
          nlinarith [sq_nonneg (y - 3 : ℤ), sq_nonneg (x - 3 : ℤ), sq_nonneg ((x : ℤ) - (y : ℤ)), sq_nonneg ((x : ℤ) - 3), sq_nonneg ((y : ℤ) - 3)]
        interval_cases x <;> omega
      omega
    interval_cases x <;> interval_cases y
    <;> norm_num [Prod.ext_iff] at h17 ⊢
    <;> tauto