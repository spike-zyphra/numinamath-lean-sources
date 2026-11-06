import Mathlib

theorem algebra_608407 :
    IsGreatest { n : ℤ | n > 0 ∧ ∃ t : ℤ, t ^ 3 = n ^ 3 + 4 * n ^ 2 - 15 * n - 18 } 19 := by
  constructor
  · -- Show 19 is in the set
    constructor
    · norm_num
    · use 20
      norm_num
  · -- Show that no integer greater than 19 is in the set
    intro n hn
    rcases hn with ⟨hn_pos, t, ht⟩
    by_contra h
    push_neg at h
    have h1 : n > 19 := h
    have h2 : t ^ 3 = n ^ 3 + 4 * n ^ 2 - 15 * n - 18 := ht
    have h3 : t > n := by
      have h4 : t ^ 3 > n ^ 3 := by 
        nlinarith
      have h5 : t > n := by
        nlinarith [sq_nonneg (t - n : ℤ), sq_nonneg (n + t : ℤ)]
      linarith
    have h5 : t < n + 2 := by
      nlinarith [sq_nonneg (t - (n + 1) : ℤ), sq_nonneg (t + (n + 1) : ℤ), sq_pos_of_pos (show 0 < (n : ℤ) by linarith)]
    have h6 : t ≤ n + 1 := by
      omega
    have h7 : t = n + 1 := by
      nlinarith
    rw [h7] at ht
    have h8 : n ^ 2 - 18 * n - 19 = 0 := by
      nlinarith
    have h9 : n ≤ 19 := by
      nlinarith [sq_nonneg (n - 19 : ℤ)]
    linarith