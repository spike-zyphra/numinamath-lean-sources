import Mathlib

/- If $x + \frac{1}{x} = 5,$ then compute the value of
\[(x - 2)^2 + \frac{25}{(x - 2)^2}.\] -/
theorem algebra_12596 {x : ℝ} (hx : x ≠ 0) (h : x + 1/x = 5) :
    (x - 2)^2 + 25/(x - 2)^2 = 11 := by
  have hx2 : x ≠ 2 := by
    rintro rfl
    norm_num at h
  field_simp [hx, hx2, sub_eq_zero, add_comm] at h ⊢
  nlinarith