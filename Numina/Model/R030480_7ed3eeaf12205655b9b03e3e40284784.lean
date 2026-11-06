import Mathlib

theorem number_theory_195751 {n : ℕ} (hn : n ≠ 0) (h : 270 % n = 0 ∧ 180 % n = 0 ∧ 235 % n = 0)
    (h' : (270 / n) * 2 = (180 / n) * 3 ∧ (180 / n) * 1 = (235 / n)) :
    n = 29 := by
  have h1 : 270 % n = 0 := h.1
  have h2 : 180 % n = 0 := h.2.1
  have h3 : 235 % n = 0 := h.2.2
  have h4 : (270 / n) * 2 = (180 / n) * 3 := h'.1
  have h5 : (180 / n) * 1 = (235 / n) := h'.2
  have h6 : 180 / n = 235 / n := by
    omega
  have h7 : n ∣ 270 := by
    exact Nat.dvd_of_mod_eq_zero h1
  have h8 : n ∣ 180 := by
    exact Nat.dvd_of_mod_eq_zero h2
  have h9 : n ∣ 235 := by
    exact Nat.dvd_of_mod_eq_zero h3
  have h10 : n ∣ 5 := by
    exact Nat.dvd_gcd (Nat.dvd_gcd h7 h8) h9
  have h11 : n ≤ 5 := by
    exact Nat.le_of_dvd (by norm_num) h10
  interval_cases n <;> norm_num at h6 h4 h1 h2 h3