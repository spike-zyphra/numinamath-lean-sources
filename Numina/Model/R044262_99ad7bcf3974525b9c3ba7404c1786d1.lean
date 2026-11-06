import Mathlib

theorem number_theory_99574 {n m k : ℕ} (hn : n > 1) (hm : m > 1) (hk : k > 1)
    (hnm : n * m = 715) (hmk : m * k < n) (hnmk : n * k < m) :
    k = 11 := by

  have h1 : n * m = 715 := hnm

  have h2 : n ≤ 18 := by
    by_contra h 
    push_neg at h
    have h3 : n ≥ 19 := by
      omega
    have h4 : m ≤ 37 := by
      nlinarith
    have h5 : n * k < m := hnmk
    have h6 : k ≥ 2 := by 
      omega
    have h7 : n * 2 < m := by
      nlinarith
    nlinarith

  have h8 : m ≤ 18 := by 
    by_contra h 
    push_neg at h 
    have h9 : m ≥ 19 := by
      omega 
    have h10 : m * k < n := hmk 
    have h11 : k ≥ 2 := by 
      omega
    have h12 : m * 2 < n := by 
      nlinarith 
    nlinarith [show n * m = 715 by linarith]

  have h9 : n * m = 715 := hnm 
  have h10 : n ≤ 18 := h2 
  have h11 : m > 1 := hm

  interval_cases n <;> omega