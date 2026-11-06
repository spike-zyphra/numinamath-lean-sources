import Mathlib

open Real

-- x ^ logb b y = y ^ logb b x for all positive x and y.
lemma lemma_1 {x y b : ℝ} (hx : 0 < x) (hy : 0 < y)  : x ^ logb b y = y ^ logb b x := by
  -- We have x ^ logb b y = exp (log x * log y / log b) and
  -- y ^ logb b x = exp (log y * log x / log b).
  rw [rpow_def_of_pos hx, rpow_def_of_pos hy]
  simp [logb]
  ring

/- 7.228. $5^{\lg x}=50-x^{\lg 5}$. -/
theorem algebra_167491 (x : ℝ) (hx : 0 < x) : 5 ^ Real.logb 10 x = 50 - x ^ Real.logb 10 5 ↔ x = 100 := by
  -- lemma_1 implies that x ^ logb 10 5 = 5 ^ logb 10 x.
  nth_rw 2 [lemma_1 (by linarith) (by linarith)]
  symm
  constructor
  · -- Assume that x = 100 and show that
    -- 5 ^ logb 10 x = 50 - 5 ^ logb 10 x.
    intro h
    subst x
    -- We have 100 = 10^2, so logb 10 x = 2.
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num]
    simp [logb_pow]
    norm_num
  -- Suppose that 5 ^ logb 10 x = 50 - 5 ^ logb 10 x.
  -- Show taht x = 100.
  intro h
  -- We get (5 : ℝ) ^ logb 10 x = 5 ^ (2 : ℝ).
  replace h : (5 : ℝ) ^ logb 10 x = 5 ^ (2 : ℝ) := by linarith
  -- We obtain logb 10 x = 2.
  repeat rw [rpow_def_of_pos (by norm_num)] at h
  simp [show (5 : ℝ) ≠ -1 by norm_num] at h
  -- logb 10 x = 2 iff 10^2 = x, i.e., x = 100.
  rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hx] at h
  linarith