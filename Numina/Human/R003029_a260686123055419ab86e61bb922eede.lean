import Mathlib

theorem algebra_146586 {l w h : ℝ} (hw : w ≠ 0) (hw' : w ≠ 0) (hw'' : h ≠ 0)
    (h1 : (l - 2) * w * h = l * w * h - 48) (h2 : l * (w + 3) * h = l * w * h + 99)
    (h3 : l * w * (h + 4) = l * w * h + 352) :
    2 * (l * w + w * h + l * h) = 290 := by
  have wh_eq : w * h = 24 := by
    linarith
  have lh_eq : l * h = 33 := by
    linarith
  have lw_eq : l * w = 88 := by
    linarith
  have surface_eq : 2 * (l * w + w * h + l * h) = 290 := by 
    rw [lw_eq, wh_eq, lh_eq]
    norm_num
  exact surface_eq