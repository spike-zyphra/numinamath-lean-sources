import Mathlib

theorem number_theory_167620 (a b c : ℕ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
    (h1 : Nat.digits a 2017 = [1, 2, 0, 1, 3, 3]) (h2 : ∃ k, Nat.digits b (2017 - k) = [1, 3, 2, 0, 1])
    (h3 : ∃ m, Nat.digits c (2017 - m) = [2, 0, 1, 3, 3]) :
    a + b + c = 22 := by

  have h6 : Nat.ofDigits a (Nat.digits a 2017) = 2017 := by
    rw [Nat.ofDigits_digits]
    all_goals omega

  rw [h1] at h6

  simp [Nat.ofDigits, mul_add, add_mul] at h6

  by_cases h7 : a ≤ 4
  · -- If a ≤ 4, then a can only be 2, 3, or 4.
    interval_cases a <;> omega

  · -- a > 4
    have ha8 : a ≥ 5 := by 
      omega

    -- Show the value of the polynomial is greater than 2017 for a ≥ 5
    have h8 : 1 + 2 * a + a ^ 3 + 3 * a ^ 4 + 3 * a ^ 5 > 2017 := by 
      have ha9 : a ≥ 5 := ha8
      have h10 : a ^ 3 ≥ 125 := by 
        have : a ≥ 5 := ha9
        have h11 : a ^ 3 ≥ 5 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left 
          all_goals omega
        norm_num at h11 ⊢ 
        omega

      have h11 : a ^ 4 ≥ 625 := by 
        have : a ≥ 5 := ha9
        have h12 : a ^ 4 ≥ 5 ^ 4 := by
          apply Nat.pow_le_pow_of_le_left 
          all_goals omega 
        norm_num at h12 ⊢ 
        omega

      have h12 : a ^ 5 ≥ 3125 := by 
        have : a ≥ 5 := ha9 
        have h13 : a ^ 5 ≥ 5 ^ 5 := by 
          apply Nat.pow_le_pow_of_le_left 
          all_goals omega 
        norm_num at h13 ⊢ 
        omega

      nlinarith

    nlinarith