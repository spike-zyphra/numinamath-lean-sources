import Mathlib

theorem algebra_188859 {x y : ℕ} (h : x * 14 + y * 3 = 107) (h' : |(x : ℤ) - y| ≤ 5) :
    x + y = 10 := by
  have h1 : (x : ℤ) * 14 + (y : ℤ) * 3 = 107 := by
    exact_mod_cast h
  have h2 : -5 ≤ (x : ℤ) - (y : ℤ) := by
    linarith [abs_le.mp h']
  have h3 : (x : ℤ) - (y : ℤ) ≤ 5 := by
    linarith [abs_le.mp h']
  have h4 : (x + y : ℤ) = 10 := by
    omega
  have h5 : x + y = 10 := by
    exact_mod_cast h4
  linarith