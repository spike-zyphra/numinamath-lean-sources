import Mathlib

theorem number_theory_320893 (n : ℕ) (hn : n > 0) (h : n % 3 + n % 6 + n % 9 = 15) :
    n % 18 = 17 := by

  have h1 : n % 3 = 2 := by 
    omega
  have h2 : n % 6 = 5 := by
    omega
  have h3 : n % 9 = 8 := by
    omega

  have h5 : n % 18 = 17 := by
    omega
  exact h5