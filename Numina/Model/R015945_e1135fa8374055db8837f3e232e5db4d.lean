import Mathlib

theorem number_theory_290849 (d r : ℕ) (h₀ : d > 0) (h₁ : 468 % d = r) (h₂ : 636 % d = r)
    (h₃ : 867 % d = r) :
    d + r ≤ 27 := by
  have h4 : d ∣ 168 := by
    have h6 : (636 : ℕ) % d = (468 : ℕ) % d := by
      omega
    -- From equality of remainders, derive divisibility
    have h11 : d ∣ (636 : ℕ) - (468 : ℕ) := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h6)
    have h12 : (636 : ℕ) - (468 : ℕ) = (168 : ℕ) := by
      norm_num
    rw [h12] at h11
    exact h11
  -- Show that $d$ divides 231
  have h5 : d ∣ 231 := by
    have h7 : (867 : ℕ) % d = (636 : ℕ) % d := by
      omega
    -- From equality of remainders, derive divisibility
    have h11 : d ∣ (867 : ℕ) - (636 : ℕ) := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h7)
    have h12 : (867 : ℕ) - (636 : ℕ) = (231 : ℕ) := by
      norm_num
    rw [h12] at h11
    exact h11
  -- GCD of 168 and 231 is 21
  have h6 : d ∣ 21 := by
    exact Nat.dvd_gcd h4 h5
  -- If $d$ divides 21, then $d \leq 21$
  have h7 : d ≤ 21 := by
    exact Nat.le_of_dvd (by linarith) h6
  interval_cases d <;> try { 
    simp_all [Nat.add_comm]
    <;> omega 
  }
  <;> try { 
    omega 
  }