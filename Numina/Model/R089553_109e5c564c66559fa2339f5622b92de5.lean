import Mathlib

theorem number_theory_133685 : IsGreatest {n | n % 20 = n / 20} 399 := by 
  constructor
  · -- Show that 399 is in the set
    show 399 % 20 = 399 / 20
    norm_num 
  · -- Show that for any n in the set, n ≤ 399
    intro n hn
    have h : n % 20 = n / 20 := hn 
    by_contra h1
    push_neg at h1 
    have h2 : n ≥ 400 := by omega 
    have h3 : n = 21 * (n / 20) := by 
      omega 
    have h4 : n / 20 ≥ 20 := by 
      omega 
    have h5 : n % 20 < 20 := by 
      omega 
    omega