import Mathlib

theorem number_theory_65322 :
    (IsGreatest {n | (2^n : ℤ) ∣ 2007^1024 - 1} 13) := by
  constructor
  · -- Show 13 is in the set
    norm_num
  · -- Show any element in the set is ≤ 13
    intro n hn
    have h : (2^n : ℤ) ∣ 2007^1024 - 1 := hn
    by_contra h'
    push_neg at h'
    have h14 : n ≥ 14 := by omega
    have h2 : ¬ (2^14 : ℤ) ∣ 2007^1024 - 1 := by
      norm_num
    have h3 : (2 ^ n : ℤ) ∣ 2007^1024 - 1 := h
    have h4 : (2^14 : ℤ) ∣ (2007^1024 - 1) := by
      have h5 : (2 ^ n : ℤ) ∣ (2007^1024 - 1) := h
      have h6 : (2^14 : ℤ) ∣ (2^n : ℤ) := by
        have h7 : n ≥ 14 := by omega
        exact pow_dvd_pow _ (show 14 ≤ n by omega)
      exact dvd_trans h6 h5
    contradiction