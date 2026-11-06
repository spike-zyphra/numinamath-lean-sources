import Mathlib

theorem number_theory_6886
(a b c : ℕ)
(h₀ : 0 < a)
(h₁ : 0 < b)
(h₂ : 0 < c)
(h₃ : Nat.gcd a b = 1)
(h₄ : c ∣ a) :
Nat.gcd b c = 1 := by
  have h7 : c ∣ a := h₄

  have h8 : Nat.gcd b c ∣ b := by
    exact Nat.gcd_dvd_left b c

  have h9 : Nat.gcd b c ∣ c := by
    exact Nat.gcd_dvd_right b c
  
  have h10 : Nat.gcd b c ∣ a := by
    exact Nat.dvd_trans h9 h7

  have h11 : Nat.gcd b c ∣ Nat.gcd a b := by 
    exact Nat.dvd_gcd h10 h8 

  rw [h₃] at h11
  have h12 : Nat.gcd b c ∣ 1 := h11

  exact Nat.eq_one_of_dvd_one h12