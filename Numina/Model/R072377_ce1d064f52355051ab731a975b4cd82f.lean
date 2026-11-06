import Mathlib

theorem algebra_122141 (d t : ℝ) (ht : t ≠ 0) (h1 : d / 90 = t - 1) (h2 : d / 60 = t + 1) :
    IsLeast {v | d / v = t} 72 := by
  have eq1 : d = 90 * (t - 1) := by
    field_simp at h1 ⊢
    linarith
  have eq2 : d = 60 * (t + 1) := by
    field_simp at h2 ⊢
    linarith
  have ht_eq : t = 5 := by
    linarith [eq1, eq2]
  have hd : d = 360 := by
    rw [ht_eq] at eq1
    linarith
  constructor
  · -- Show that 72 is in the set
    rw [Set.mem_setOf_eq]
    rw [hd, ht_eq]
    norm_num
  · -- Show that for all v in the set, 72 ≤ v
    intro v hv
    rw [Set.mem_setOf_eq] at hv
    rw [hd, ht_eq] at hv
    have h3 : v ≠ 0 := by
      by_contra h
      rw [h] at hv
      norm_num at hv
      all_goals linarith
    field_simp [h3] at hv
    have h4 : v = 72 := by
      linarith
    linarith [h4]