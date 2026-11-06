import Mathlib

open Nat

theorem number_theory_270171 (a m : ℕ) (_ : Nat.Coprime a m) (hm : 1 < m) :
    ∀ b : ℤ, ∃ x : ℤ, (a * x - b) % m = 0 := by
  intro b
  have h1 : IsCoprime (a : ℤ) (m : ℤ) := by
    exact Int.coprime_iff_nat_coprime.mpr (show Nat.Coprime a m by assumption)
  rcases h1 with ⟨x, y, h2⟩
  use b * x 
  have h6 : (a * (b * x) - b) = - (b * (m * y)) := by 
    have h7 : (a : ℤ) * x + (m : ℤ) * y = 1 := by 
      linarith 
    have h8 : (a : ℤ) * (b * x) + (m : ℤ) * (b * y) = b := by
      calc
        (a : ℤ) * (b * x) + (m : ℤ) * (b * y) = b * ((a : ℤ) * x + (m : ℤ) * y) := by ring
        _ = b * 1 := by 
          rw [h7]
        _ = b := by ring
    linarith
  have h3 : (m : ℤ) ∣ (a * (b * x) - b) := by
    rw [h6]
    have h7 : (m : ℤ) ∣ (b * (m * y)) := by 
      use (b * y)
      all_goals ring
    have h8 : (m : ℤ) ∣ - (b * (m * y)) := by 
      exact dvd_neg.mpr h7 
    exact h8 
  have h4 : (a * (b * x) - b) % m = 0 := by 
    have h5 : (m : ℤ) ∣ (a * (b * x) - b) := h3 
    exact Int.emod_eq_zero_of_dvd h5 
  exact h4