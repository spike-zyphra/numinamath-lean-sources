import Mathlib

theorem algebra_11283 : IsGreatest {x : ℕ | x * 1350 ≤ 10000} 7 := by
  constructor
  · -- Show that 7 is in the set
    show 7 * 1350 ≤ 10000
    norm_num

  · -- Show that for all x in the set, x ≤ 7
    intro x
    intro hx

    have h : x * 1350 ≤ 10000 := hx

    by_contra h1
    push_neg at h1
    have h2 : x ≥ 8 := by omega

    have h3 : x * 1350 > 10000 := by
      have h4 : x ≥ 8 := h2
      have h5 : x * 1350 ≥ 8 * 1350 := by
        nlinarith
      have h6 : 8 * 1350 > 10000 := by norm_num
      linarith

    linarith