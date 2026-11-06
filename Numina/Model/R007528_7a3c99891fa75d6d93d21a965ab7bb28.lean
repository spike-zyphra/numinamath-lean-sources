import Mathlib

theorem algebra_17157 : IsGreatest {n : ℕ | n * 25 + n * 5 ≤ 320} 10 := by
  constructor
  · -- Show 10 is in the set
    show 10 * 25 + 10 * 5 ≤ 320
    norm_num
  · -- Show there is no greater element in the set
    intro n hn
    have h : n * 25 + n * 5 ≤ 320 := by
      simpa using hn
    by_contra h'
    push_neg at h'
    have h1 : n ≥ 11 := by omega
    have h2 : n * 25 + n * 5 > 320 := by
      have h3 : n ≥ 11 := h1
      have h4 : n * 25 + n * 5 = n * 30 := by
        omega
      have h5 : n * 30 ≥ 330 := by
        nlinarith
      omega
    omega