import Mathlib

theorem algebra_326614 : IsGreatest {n | ∀ i ∈ Finset.range 10, n ∣ (1983 + i)^3 + 3 * (1983 + i)^2 + 2 * (1983 + i)} 6 := by 
  constructor
  · -- Show 6 is in the set.
    intro i hi
    have h1 : i < 10 := by 
      simp [Finset.mem_range] at hi ⊢
      omega
    interval_cases i <;> norm_num
  · -- Show that any element in the set divides 6.
    intro n hn
    have h1 := hn 0 (by simp)
    have h2 := hn 1 (by simp)
    have h3 := hn 2 (by simp)
    have h4 := hn 3 (by simp)
    have h5 := hn 4 (by simp)
    have h6 := hn 5 (by simp)
    have h7 := hn 6 (by simp)
    have h8 := hn 7 (by simp)
    have h9 := hn 8 (by simp)
    have h10 := hn 9 (by simp)
    norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 
    -- Calculate GCD of all expressions and show it's 6
    have h11 : n ∣ 6 := by
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3) h4) h5) h6) h7) h8) h9) h10
    exact Nat.le_of_dvd (by norm_num) h11