import Mathlib

theorem algebra_110793 {N : ℕ} (hN : N > 0) (x : ℝ) (hx : x > 0)
    (h : (N * (1 + x) - x) / N = 1 + x) :
    x ≤ 1 / 2 := by
  have hN' : (N : ℝ) > 0 := by exact_mod_cast hN
  field_simp [(show (N : ℝ) ≠ 0 by positivity)] at h
  -- At this point, h simplifies to 'N * (1 + x) - x = N * (1 + x)' which simplifies to x = 0
  -- But given hx: x > 0 contradicts that, so nlinarith can solve the contradiction
  all_goals nlinarith