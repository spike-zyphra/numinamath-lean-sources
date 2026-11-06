import Mathlib

theorem number_theory_196717 :
    IsGreatest {n | 0 < n ∧ (n + 10) ∣ n^3 + 100} 890 := by
  constructor
  · -- Show that 890 is in the set.
    constructor
    · -- Show that 890 is positive.
      norm_num
    · -- Show that 890 + 10 divides 890^3 + 100.
      norm_num
  · -- Show that for any n in the set, n ≤ 890.
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    have h1 : (n + 10 : ℤ) ∣ (n^3 + 100 : ℤ) := by
      exact_mod_cast hn_div
    have h2 : (n + 10 : ℤ) ∣ ((n : ℤ)^3 + 1000) := by
      use (n^2 - 10*n + 100 : ℤ)
      ring_nf
    have h3 : (n + 10 : ℤ) ∣ ((n : ℤ)^3 + 1000 - ((n : ℤ)^3 + 100)) := by 
      apply Dvd.dvd.sub h2 h1
    have h4 : (n + 10 : ℤ) ∣ 900 := by 
      have h5 : ((n : ℤ)^3 + 1000 - ((n : ℤ)^3 + 100)) = (900 : ℤ) := by 
        ring
      rw [h5] at h3 
      exact_mod_cast h3
    have h5 : (n + 10 : ℤ) ≤ 900 := by 
      apply Int.le_of_dvd (by omega) h4 
    have h6 : n ≤ 890 := by 
      omega 
    exact h6