import Mathlib

theorem algebra_299311 {x : ℝ} (hx : x ≠ 0) (h : (x - 50000) / (x - 50000 - 10000) = x / (x - 10000)) :
    x = 120000 := by
  have h1 : x - 50000 - 10000 ≠ 0 := by
    by_contra h1
    have h2 : x = 60000 := by linarith
    rw [h2] at h
    norm_num at h
  have h2 : x - 10000 ≠ 0 := by
    by_contra h2
    have h3 : x = 10000 := by linarith
    rw [h3] at h
    norm_num at h
  have h3 : (x - 50000) / (x - 50000 - 10000) = x / (x - 10000) := h
  have h4 : (x - 50000) * (x - 10000) = x * (x - 50000 - 10000) := by
    field_simp [h1, h2] at h3 ⊢
    nlinarith
  have h5 : (x - 50000) * (x - 10000) = x * (x - 60000) := by
    linarith [h4]
  have h6 : (x - 50000) * (x - 10000) - x * (x - 60000) = 0 := by
    linarith [h5]
  -- Expanding left side: $(x - 50000)(x - 10000) -x(x - 60000) = (x^2 -60000x +500000000 ) - (x^2 -60000x ) =500000000$
  -- Right side is 0
  -- So $500000000 =0$, a contradiction.
  nlinarith