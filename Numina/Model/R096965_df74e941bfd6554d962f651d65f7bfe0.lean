import Mathlib

theorem algebra_42642 {p : ℝ → ℝ} (hp : p = fun x => x ^ 3 - 3 * x ^ 2 + 5 * x)
    (h k : ℝ) (hh : p h = 1) (hk : p k = 5) : h + k = 2 := by
  simp [hp] at hh hk
  nlinarith [sq_nonneg (h - k), sq_nonneg (h + k - 2), sq_nonneg (h - 1), sq_nonneg (k - 1), 
          sq_nonneg (h - 2), sq_nonneg (k - 2), sq_nonneg (h^2 - k^2), sq_nonneg (h * k - 1)]