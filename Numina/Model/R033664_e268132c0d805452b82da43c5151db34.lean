import Mathlib

theorem algebra_313671 {f : ℝ → ℝ} (h : ∀ x y, (x + y) * (f x - f y) = (x - y) * f (x + y)) :
    ∃ a b, f = fun x => a * x ^ 2 + b * x := by

  have h1 : f 0 = 0 := by
    specialize h 1 (-1)
    norm_num at h
    linarith

  use (f 1 + f (-1)) / 2, (f 1 - f (-1)) / 2

  funext x
  have eq2 := h x 1
  have eq3 := h x (-1)
  have eq4 := h 1 (-1)
  have eq5 := h (x + 1) (-1)

  simp [show f 0 = (0 : ℝ) by linarith [h1]] at eq2 eq3 eq4 eq5

  have eq6 := h x (-x)
  simp [show f 0 = (0 : ℝ) by linarith [h1]] at eq6

  have eq7 : f x = (f 1 + f (-1)) / 2 * x ^ 2 + (f 1 - f (-1)) / 2 * x := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x), sq_nonneg (x - 2), sq_nonneg (x + 2)]

  linarith [eq7]