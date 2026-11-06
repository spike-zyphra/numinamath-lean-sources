import Mathlib

open Nat

theorem number_theory_5797 :
    {(a, b, c) : ℤ × ℤ × ℤ | a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a^2 + b^2 = c^2 ∧ |c| < 14}.ncard = 48 := by
  have h1 : {(a, b, c) : ℤ × ℤ × ℤ | a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a^2 + b^2 = c^2 ∧ |c| < 14} = Finset.filter (fun s : ℤ × ℤ × ℤ => 
    s.1 ≠ 0 ∧ s.2.1 ≠ 0 ∧ s.2.2 ≠ 0 ∧ s.1^2 + s.2.1^2 = s.2.2^2 ∧ |s.2.2| < 14) (Finset.Icc (-14 : ℤ) 14 ×ˢ Finset.Icc (-14 : ℤ) 14 ×ˢ Finset.Icc (-13 : ℤ) 13) := by
    ext ⟨a, b, c⟩
    simp
    intro ha hb hc h_eq h2
    have h3 : a^2 + b^2 = c^2 := h_eq
    have h4 : a^2 ≤ 196 := by 
      have h5 : c^2 < 196 := by 
        have : |c| < 14 := h2
        have h6 : c < 14 := by
          cases' abs_lt.mp this with h7 h8
          linarith
        have h7 : c > -14 := by
          cases' abs_lt.mp this with h7 h8
          linarith
        nlinarith [sq_nonneg (c : ℤ)]
      nlinarith [sq_nonneg (b : ℤ), sq_nonneg (a : ℤ)]
    have ha1 : -14 ≤ a := by nlinarith [h4]
    have ha2 : a ≤ 14 := by nlinarith [h4]
    have h5 : b^2 ≤ 196 := by 
      have h6 : c^2 < 196 := by 
        have : |c| < 14 := h2
        have h7 : c < 14 := by
          cases' abs_lt.mp this with h8 h9
          linarith
        have h8 : c > -14 := by
          cases' abs_lt.mp this with h8 h9
          linarith
        nlinarith [sq_nonneg (c : ℤ)]
      nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ)]
    have hb1 : -14 ≤ b := by nlinarith [h5]
    have hb2 : b ≤ 14 := by nlinarith [h5]
    have hc1 : -13 ≤ c := by 
      cases' abs_lt.mp h2 with h3 h4
      linarith
    have hc2 : c ≤ 13 := by 
      cases' abs_lt.mp h2 with h3 h4
      linarith
    omega
  rw [h1] at *
  rw [Set.ncard_coe_Finset] at *
  native_decide