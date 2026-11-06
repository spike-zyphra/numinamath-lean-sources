import Mathlib

theorem number_theory_3290 (n : ℕ) (h₀ : n > 0) (h₁ : (Nat.digits 10 n).sum = 2019) :
    (Nat.digits 10 n).length ≥ 225 := by 
  by_contra h
  push_neg at h 
  have h2 : (Nat.digits 10 n).length ≤ 224 := by
    omega
  have h7 : (Nat.digits 10 n).sum ≤ 2016 := by
    have h9 : ∀ d ∈ (Nat.digits 10 n), d ≤ 9 := by 
      intro d hd
      have h10 : d < 10 := by
        have h11 : d ∈ (Nat.digits 10 n) := hd
        have h9_lt : d < 10 := by
          exact Nat.digits_lt_base (by norm_num) h11
        omega
      omega
    have h10 : (Nat.digits 10 n).sum ≤ (Nat.digits 10 n).length * 9 := by
      have h11 : (Nat.digits 10 n).sum ≤ (Nat.digits 10 n).length * 9 := by
        apply List.sum_le_card_nsmul
        intro d hd
        specialize h9 d hd
        all_goals linarith
      linarith
    nlinarith [h10, h2]
  omega