import Mathlib

theorem number_theory_4776 {a p : ℕ} (hp : p.Prime) (_ : 0 < a) (hap : ¬p ∣ a) :
    a^(p-1) ≡ 1 [MOD p] := by 
  have ha1 : Nat.Coprime a p := by 
    rw [Nat.Coprime]
    have h1 : p.Prime := hp
    have h5 : Nat.gcd a p ∣ a := by
      apply Nat.gcd_dvd_left
    have h6 : Nat.gcd a p ∣ p := by 
      apply Nat.gcd_dvd_right
    have h7 : Nat.gcd a p = 1 ∨ Nat.gcd a p = p := by
      have h8 : p.Prime := hp
      have h9 : Nat.gcd a p ∣ p := by 
        apply Nat.gcd_dvd_right
      have h10 : Nat.gcd a p = 1 ∨ Nat.gcd a p = p := by 
        apply (Nat.dvd_prime (show Nat.Prime p by exact hp)).mp 
        exact_mod_cast h9
      exact_mod_cast h10 
    rcases h7 with (h_eq_1 | h_eq_p)
    · 
      exact_mod_cast h_eq_1 
    ·
      have h2 : p ∣ a := by 
        have h15 : Nat.gcd a p ∣ a := by
          apply Nat.gcd_dvd_left 
        have h3 : Nat.gcd a p = p := h_eq_p
        rw [h3] at h15 
        exact_mod_cast h15 
      exfalso 
      exact_mod_cast (show ¬p ∣ a by exact_mod_cast hap) h2 
  have h1 : a ^ (p.totient) ≡ 1 [MOD p] := 
    Nat.ModEq.pow_totient ha1
  have h2 : p.totient = p - 1 := 
    Nat.totient_prime hp
  rw [h2] at h1 
  exact_mod_cast h1