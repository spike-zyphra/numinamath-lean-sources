import Mathlib

theorem number_theory_110900 (n : ℕ) (h₁ : 2 ∣ n) (h₂ : 3 ∣ n) : 6 ∣ n := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨k, hk⟩ := h₂
  have h4 : 2 * m = 3 * k := by
    linarith 
  have h6 : 2 ∣ 3 * k := by 
    omega 
  have h7 : Nat.gcd 2 3 = 1 := by 
    norm_num 
  have h8 : 2 ∣ k := by 
    apply Nat.Coprime.dvd_of_dvd_mul_left h7 h6 
  rcases h8 with ⟨t, ht⟩ 
  use t 
  linarith 
  all_goals omega