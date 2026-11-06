import Mathlib

theorem algebra_7675 {x : ℝ} (hx : x > 0) (h : x = (1/4) * x ^ ((1 : ℝ)/3)) :
x = 1 / 8 := by
  have h1 : x ^ ((1 : ℝ) / 3) = x ^ (1 / 3 : ℝ) := by
    norm_num
  -- From `h: x = (1/4) * x^((1 : ℝ)/3)`, rewrite with the simplified power.
  have hq : x ^ (1 / 3 : ℝ) = 4 * x := by
    have h2 := h
    have eq1 : x ^ ((1 : ℝ) / 3) = x ^ (1 / 3 : ℝ) := h1
    rw [eq1] at h2
    nlinarith
  have hx2 : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  -- From `hq` and `hx2` derive x^3.
  have hx3 : x^3 = (1 / 64) * x := by
    have eq1 : x ^ (1 / 3 : ℝ) = 4 * x := hq
    have eq2 : (x ^ (1 / 3 : ℝ)) ^ 3 = x := hx2
    have eq3 : (4 * x) ^ 3 = x := by
      calc
        (4 * x) ^ 3 = (x ^ (1 / 3 : ℝ)) ^ 3 := by
          rw [eq1]
        _ = x := eq2
    nlinarith [sq_nonneg (x), sq_nonneg (x ^ 2)]
  -- Rearranging hx3 to form a polynomial equation.
  have h4 : x ^ 3 - (1 / 64) * x = 0 := by linarith [hx3]
  have h5 : x * (x ^ 2 - (1 / 64 : ℝ)) = 0 := by
    nlinarith [h4]
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- inconsistency, x>0
    nlinarith
  · -- Now we have x^2 -1/64 =0
    have h8 : x ^ 2 = 1 / 64 := by
      nlinarith
    have h9 : x > 0 := by linarith
    nlinarith [sq_nonneg (x - (1 / 8) ), h8]