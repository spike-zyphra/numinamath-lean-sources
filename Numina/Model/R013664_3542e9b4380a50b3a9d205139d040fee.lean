import Mathlib

theorem number_theory_180838 (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ∀ q > 0, ∃ r : ℚ, r > 0 ∧ q = (r * x) % 1 / (r * y) % 1) :
    x * y < 0 := by
  by_contra h1
  push_neg at h1
  have h2 := h (1 + (x * y) ) (by
    have h2 : x * y ≥ 0 := h1
    nlinarith
  )
  rcases h2 with ⟨r, hr, hq⟩
  norm_num [Rat.num, Rat.den] at hq
  all_goals
    nlinarith [sq_pos_of_pos hr, sq_nonneg (r * x - r * y), sq_nonneg (r * x + r * y), sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_nonneg (x), sq_nonneg (y), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x + y)]