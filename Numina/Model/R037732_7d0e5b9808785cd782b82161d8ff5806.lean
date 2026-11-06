import Mathlib

theorem number_theory_16627 :
    IsGreatest {n | n < 0 ∧ (Nat.digits 10 ((-n).toNat)).length = 4 ∧ n ≡ 1 [ZMOD 23]} (-1011) := by
  constructor
  · -- Show -1011 is in the set.
    constructor
    · -- Show -1011 is negative
      norm_num
    constructor
    · -- Show that -1011 has 4 digits
      native_decide
    · -- Show -1011 ≡ 1 [ZMOD 23]
      native_decide
  · -- Show that -1011 is greatest in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3⟩
    have h1 : n < 0 := hn1
    have h2 : (Nat.digits 10 ((-n).toNat)).length = 4 := hn2
    have h3 : n ≡ 1 [ZMOD 23] := hn3
    have h4 : (-n).toNat ≥ 1000 := by
      by_contra h
      push_neg at h
      have h5 : (Nat.digits 10 ((-n).toNat)).length < 4 := by
        interval_cases h6 : (-n).toNat <;> norm_num at *
      linarith
    have h5 : (-n).toNat < 10000 := by
      by_contra h
      push_neg at h
      have h8 : (Nat.digits 10 ((-n).toNat)).length > 4 := by
        have h7 : (-n).toNat ≥ 10000 := by omega
        have h8 : (Nat.digits 10 ((-n).toNat)).length > 4 := by
          have h9 : Nat.log 10 ((-n).toNat) ≥ 4 := by
            apply Nat.le_log_of_pow_le (by omega) h7
          have h10 : (Nat.digits 10 ((-n).toNat)).length = Nat.log 10 ((-n).toNat) + 1 := by
            rw [Nat.digits_len]
            all_goals
              omega
          linarith
        linarith
      linarith
    have h6 : n ≤ -1000 := by
      have h8 : (-n).toNat ≥ 1000 := h4
      have h8a : (n : ℤ) ≤ -1000 := by
        by_contra h
        push_neg at h
        have h10 : n > -1000 := by omega
        have h11 : n ≥ -999 := by omega
        have h12 : (-n).toNat < 1000 := by
          omega
        linarith
      linarith
    have h7 : n ≥ -9999 := by
      have h9 : (-n).toNat < 10000 := h5
      have h10 : (n : ℤ) ≥ -9999 := by
        by_contra h
        push_neg at h
        have h11 : (n : ℤ) ≤ -10000 := by omega
        have h12 : (-n).toNat ≥ 10000 := by
          omega
        linarith
      linarith
    norm_num [Int.ModEq] at h3
    omega