import Mathlib

theorem algebra_19923 : IsLeast {x : ℤ | 12 % (x + 1) = 0} (-13) := by
  constructor
  · -- First, we verify that -13 is in the set.
    show 12 % (-13 + 1) = 0
    norm_num
  · -- Now we show that -13 is minimal, meaning that if x is in the set and x < -13, then x is invalid.
    intro x hx
    have h1 : 12 % (x + 1) = 0 := hx
    by_contra h
    push_neg at h
    have h2 : x ≤ -14 := by linarith
    have h3 : x + 1 ≤ -13 := by linarith
    have h4 : x + 1 ≤ -13 := h3
    have h5 : x + 1 < 0 := by linarith
    have h6 : x + 1 ∣ 12 := by
      have h7 : 12 % (x + 1) = 0 := h1
      exact Int.dvd_of_emod_eq_zero h7
    have h7 : x + 1 ≤ -13 := h4
    have h8 : x + 1 ∣ 12 := h6
    have h9 : x + 1 ≥ -12 := by
      have h2 : (x + 1) ∣ 12 := h6
      have h7 : -(x + 1) ∣ 12 := by 
        exact Int.neg_dvd.2 h2
      have h8 : -(x + 1) ≤ 12 := by 
        apply Int.le_of_dvd (by norm_num) h7
      omega
    linarith