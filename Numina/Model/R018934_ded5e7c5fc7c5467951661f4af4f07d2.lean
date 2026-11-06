import Mathlib

theorem algebra_231702 (a : ℕ → ℝ) (ha : a 0 = 8) (ha' : a 9 = 26)
    (h : ∀ n, a (n + 2) = (∑ i in Finset.range (n + 3), a i) / (n + 3)) :
    a 1 = 44 := by
  have a2_eq : a 2 = (8 + a 1) / 2 := by
    have h2 := h 0
    norm_num [Finset.sum_range_succ, ha] at h2
    nlinarith

  have a3_eq : a 3 = (8 + a 1) / 2 := by
    have h3 := h 1
    norm_num [Finset.sum_range_succ, ha, a2_eq] at h3
    nlinarith

  have a4_eq : a 4 = (8 + a 1) / 2 := by
    have h4 := h 2
    norm_num [Finset.sum_range_succ, ha, a2_eq, a3_eq] at h4
    nlinarith

  have a5_eq : a 5 = (8 + a 1) / 2 := by
    have h5 := h 3
    norm_num [Finset.sum_range_succ, ha, a2_eq, a3_eq, a4_eq] at h5
    nlinarith

  have a6_eq : a 6 = (8 + a 1) / 2 := by
    have h6 := h 4
    norm_num [Finset.sum_range_succ, ha, a2_eq, a3_eq, a4_eq, a5_eq] at h6
    nlinarith

  have a7_eq : a 7 = (8 + a 1) / 2 := by
    have h7 := h 5
    norm_num [Finset.sum_range_succ, ha, a2_eq, a3_eq, a4_eq, a5_eq, a6_eq] at h7
    nlinarith

  have a8_eq : a 8 = (8 + a 1) / 2 := by
    have h8 := h 6
    norm_num [Finset.sum_range_succ, ha, a2_eq, a3_eq, a4_eq, a5_eq, a6_eq, a7_eq] at h8
    nlinarith

  have a9_eq : a 9 = (8 + a 1) / 2 := by
    have h9 := h 7
    norm_num [Finset.sum_range_succ, ha, a2_eq, a3_eq, a4_eq, a5_eq, a6_eq, a7_eq, a8_eq] at h9
    nlinarith

  rw [a9_eq] at ha'
  nlinarith