import Mathlib

theorem number_theory_130931 {N : ℕ} (hN : N ≠ 0) :
    ∀ a, Nat.Coprime a N → N ∣ a ^ (Nat.totient N) - 1 := by 
  intro a ha
  have h : a ^ (Nat.totient N) ≡ 1 [MOD N] := by
    apply Nat.ModEq.pow_totient 
    all_goals tauto 
  have h2 : (a ^ (Nat.totient N) : ℕ) ≡ (1 : ℕ) [MOD N] := by
    exact h 
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h2)