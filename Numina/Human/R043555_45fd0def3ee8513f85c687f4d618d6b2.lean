import Mathlib

open scoped Nat

/- Show that if \( a \) and \( b \) are positive integers, then the greatest common divisor \( (a, b) \) divides the least common multiple \( [a, b] \). Under what conditions does \( (a, b) = [a, b] \)?-/
theorem number_theory_4581 (a b : ℕ) (hab : 0 < a ∧ 0 < b) :
    gcd a b ∣ lcm a b ∧ ((gcd a b = lcm a b) ↔ a = b) := by
  constructor
  have h1: (gcd a b)∣a := Nat.gcd_dvd_left _ _
  have h2: a ∣ (lcm a b):=  dvd_lcm_left _ _
  -- use transitivity
  apply dvd_trans h1 h2
  -- The equality \( (a, b) = [a, b] \) holds true when \( a \) and \( b \) are equal. In this case, both the gcd and lcm of \( a \) and \( b \) will be equal to \( a \) (or \( b \)). More generally, this occurs when \( a \) and \( b \) are multiples of each other, meaning one is a scalar multiple of the other (e.g., \( b = ka \) for some integer \( k \)). 
  constructor
  intro h
  have h1 := dvd_lcm_left a b
  rw [← h] at h1
  rw [dvd_gcd_iff] at h1
  have h2 := dvd_lcm_right a b
  rw [← h] at h2
  rw [dvd_gcd_iff] at h2
  -- use a|b b|a -> a=b
  apply Dvd.dvd.antisymm'
  exact h2.1
  exact h1.2
  intro h
  rw [h]
  simp