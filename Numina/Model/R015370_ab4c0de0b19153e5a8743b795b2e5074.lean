import Mathlib


theorem algebra_169144 {x y z w : ℝ} (hw : w ≠ 0) (h1 : (x + 6 * y - 3 * z) / (-3 * x + 4 * w) = 2 / 3)
    (h2 : (-2 * y + z) / (x - w) = 2 / 3) :
    x / w = 2 / 3 := by
  have h1' : -3 * x + 4 * w ≠ 0 := by
    by_contra h
    have h3 : (x + 6 * y - 3 * z) / (-3 * x + 4 * w) = 0 := by 
      rw [show -3 * x + 4 * w = (0 : ℝ) by linarith]
      norm_num
    linarith
  have h3' : x - w ≠ 0 := by
    by_contra h
    have h4 : (-2 * y + z) / (x - w) = 0 := by 
      rw [show x - w = (0 : ℝ) by linarith]
      norm_num
    linarith
  have eq1 : 3 * (x + 6 * y - 3 * z) = 2 * (-3 * x + 4 * w) := by
    have h4 : -3 * x + 4 * w ≠ 0 := h1'
    field_simp [h4] at h1
    have h6 : (-(3 * x) + 4 * w : ℝ) ≠ 0 := by
      intro h7
      apply h4
      linarith
    have h7 : (x + 6 * y - 3 * z) * 3 = 2 * (-(3 * x) + 4 * w) := by
      field_simp [h6] at h1 ⊢
      linarith
    linarith [h7]
  have eq2 : 3 * (-2 * y + z) = 2 * (x - w) := by
    have h8 : x - w ≠ 0 := h3'
    field_simp [h8] at h2
    have h9 : (-2 * y + z) * 3 = 2 * (x - w) := by
      have h10 : (x - w) ≠ 0 := by
        intro h11
        apply h8
        all_goals linarith
      field_simp [h10] at h2 ⊢
      linarith
    linarith [h9]
  have eq3 : 9 * x + 18 * y - 9 * z - 8 * w = 0 := by
    linarith
  have eq4 : -2 * x - 6 * y + 3 * z + 2 * w = 0 := by
    linarith
  have eq6 : 3 * x - 2 * w = 0 := by
    linarith [eq3, eq4]
  have eq7 : 3 * x = 2 * w := by
    linarith
  have eq8 : x = (2 / 3) * w := by
    linarith
  have h4 : x / w = 2 / 3 := by
    rw [eq8]
    field_simp [hw]
    all_goals linarith
  exact h4