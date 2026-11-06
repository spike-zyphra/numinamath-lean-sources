import Mathlib

theorem number_theory_224199 (x y : ℤ) (h : 17 ∣ 2 * x + 3 * y) :
    17 ∣ 9 * x + 5 * y := by
  have h1 : (2 * x + 3 * y) % 17 = 0 := by 
    exact Int.dvd_iff_emod_eq_zero.mp h
  have eq2 : (2 * x) % 17 = (-3 * y) % 17 := by 
    omega
  have eq3 : (x) % 17 = (7 * y) % 17 := by 
    omega
  have eq9 : (9 * x + 5 * y) % 17 = 0 := by 
    have h2 : (2 * x) % 17 = (-3 * y) % 17 := eq2
    have eq4 : (x) % 17 = (7 * y) % 17 := eq3
    omega
  exact Int.dvd_of_emod_eq_zero eq9