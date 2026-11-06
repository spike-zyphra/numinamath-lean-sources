import Mathlib

theorem algebra_8467 {x : ℝ} (hx : x ≠ 0) (h : 90000 / x = 80000 / (x - 500)) :
    x = 4500 := by
  have hxne500 : x - 500 ≠ 0 := by
    by_contra h1
    have h1' : x = 500 := by linarith
    rw [h1'] at h
    norm_num at h
    all_goals tauto
  have h1 : 90000 * (x - 500) = 80000 * x := by
    field_simp [hx, hxne500] at h ⊢
    linarith
  linarith