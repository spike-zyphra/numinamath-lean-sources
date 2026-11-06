import Mathlib

theorem algebra_11074 :
    IsGreatest {t : ℝ | ∃ x y, t = (x + y) / x ∧ -4 ≤ x ∧ x ≤ -2 ∧ 2 ≤ y ∧ y ≤ 4} (1 / 2) := by
  constructor
  · -- Show that 1/2 is achievable, by finding specific x and y
    use -4, 2
    norm_num
  · -- Show that 1/2 is the greatest value, by proving any value in the set is ≤ 1/2
    intro t ht
    rcases ht with ⟨x, y, h1, hx1, hx2, hy1, hy2⟩
    have hx3 : x < 0 := by
      nlinarith
    have h5 : (x + y) / x ≤ 1 / 2 := by
      apply (div_le_iff_of_neg' hx3).mpr
      nlinarith
    linarith [h1, h5]