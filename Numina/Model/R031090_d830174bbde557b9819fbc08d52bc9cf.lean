import Mathlib

theorem number_theory_98158 (d : ℕ) (h : d > 1) (r : ℕ)
    (h1 : r = 1059 % d) (h2 : r = 1417 % d) (h3 : r = 2312 % d) :
    d - r = 15 := by 
  have h4 : 1059 % d = 1417 % d := by 
    omega
  have h5 : 1417 % d = 2312 % d := by 
    omega
  have h6 : d ∣ 358 := by
    have h7 : (1417 : ℕ) % d = (1059 : ℕ) % d := by 
      omega
    have h8 : d ∣ (1417 : ℕ) - (1059 : ℕ) := by 
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h7)
    have h9 : (1417 : ℕ) - (1059 : ℕ) = 358 := by 
      omega
    rw [h9] at h8
    exact h8
  have h7 : d ∣ 895 := by 
    have h8 : (2312 : ℕ) % d = (1417 : ℕ) % d := by 
      omega 
    have h9 : d ∣ (2312 : ℕ) - (1417 : ℕ) := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h8)
    have h10 : (2312 : ℕ) - (1417 : ℕ) = 895 := by 
      omega 
    rw [h10] at h9 
    exact h9 
  have h8 : d ∣ 179 := by 
    exact Nat.dvd_gcd h6 h7 
  have h9 : d = 179 := by 
    -- Now, from h8 we know $d|179$, and 179 is prime.
    have h10 : d ∣ 179 := h8 
    have h11 : d ≤ 179 := by 
      exact Nat.le_of_dvd (by linarith) h10
    have h12 : d ≥ 2 := by linarith 
    by_cases h13 : d < 179 
    · -- Assume d < 179 
      have h14 : d ≤ 178 := by omega
      interval_cases d <;> norm_num at h10 
    · -- Assume d ≥ 179 
      have h14 : d ≥ 179 := by omega 
      nlinarith 
  have h10 : r = 164 := by 
    rw [show r = 1059 % d by omega, h9] 
    all_goals norm_num 
  calc 
    d - r = 179 - 164 := by rw [h9, h10] 
    _ = 15 := by omega