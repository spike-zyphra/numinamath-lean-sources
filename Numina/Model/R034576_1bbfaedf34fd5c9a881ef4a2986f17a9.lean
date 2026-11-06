import Mathlib

theorem algebra_208429 {p : ℝ → ℝ} (hp : p = fun x => x^3 - 3 * x^2 + 5 * x)
    (h k : ℝ) (hroot : p h = 1) (kroot : p k = 5) : h + k = 2 := by
  have eq1 : h^3 - 3 * h^2 + 5 * h = 1 := by 
    rw [hp] at hroot
    simpa using hroot
  have eq2 : k^3 - 3 * k^2 + 5 * k = 5 := by
    rw [hp] at kroot 
    simpa using kroot
  have eq3 : k = 2 - h := by
    nlinarith [sq_nonneg (k - h), sq_nonneg (k - (2 - h)), sq_nonneg (h - 1), sq_nonneg (k - 1),
      sq_nonneg (h^2 - h), sq_nonneg (k^2 - k), sq_nonneg (h - k),
      sq_nonneg (h + k - 2)]
  -- Now we can prove h + k = 2
  linarith [eq3]