import Mathlib

theorem number_theory_289107 (n m l : ℕ) 
(h3 : (11 / 100 : ℝ) * n + (54 / 100 : ℝ) * m + (97 / 100 : ℝ) * l = 30 / 100 * (n + m + l)): 43 ∣ n + m + l := by
  have eq1 : (11 * (n : ℝ) + 54 * (m : ℝ) + 97 * (l : ℝ) = 30 * (n + m + l)) := by
    linarith
  have eq2 : 11 * (n : ℤ) + 54 * (m : ℤ) + 97 * (l : ℤ) = 30 * (n + m + l) := by
    exact_mod_cast eq1
  have eq3 : 19 * (n : ℤ) = 24 * (m : ℤ) + 67 * (l : ℤ) := by 
    linarith [eq2]
  have eq4 : 19 * (n : ℕ) = 24 * (m : ℕ) + 67 * (l : ℕ) := by 
    exact_mod_cast eq3
  have h4 : (n + m + l) % 43 = 0 := by
    omega
  exact Nat.dvd_of_mod_eq_zero h4