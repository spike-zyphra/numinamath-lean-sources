import Mathlib

theorem algebra_20452 (a b c : ℕ) (ha : a = 48) (hb : b = 72) (hc : c = 40) :
    IsGreatest {x | x > 0 ∧ a % x = 0 ∧ b % x = 0 ∧ c % x = 0} 8 := by 
  rw [ha, hb, hc]
  constructor
  · -- Show 8 is in the set.
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that if x is in the set, then x ≤ 8.
    intro x hx
    rcases hx with ⟨hx_pos, hx1, hx2, hx3⟩
    by_contra h
    push_neg at h

    have h2 : x ∣ 48 := by
      exact Nat.dvd_of_mod_eq_zero (show 48 % x = 0 by omega)
    have h3 : x ∣ 72 := by
      exact Nat.dvd_of_mod_eq_zero (show 72 % x = 0 by omega)
    have h4 : x ∣ 40 := by
      exact Nat.dvd_of_mod_eq_zero (show 40 % x = 0 by omega)
    
    have h5 : x ∣ 8 := Nat.dvd_gcd (Nat.dvd_gcd h2 h3) h4
    have h6 : x ≤ 8 := by
      exact Nat.le_of_dvd (by omega) h5
    omega  --Contradiction: we show ¬(8 ≤ 8).