import Mathlib

theorem algebra_140444 {x y : ℝ} (h : x / y = 3 / 7) (hx : x = 7.35) :
    y = 17.15 := by
  have h1 : y ≠ 0 := by
    by_contra h2
    rw [h2] at h
    norm_num at h
    all_goals linarith
  rw [hx] at h
  field_simp [h1] at h
  ring_nf at h ⊢
  <;> linarith