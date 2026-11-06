import Mathlib

theorem algebra_21237 {a b c d m n : ℝ} (h : m = (a + c) / 2 ∧ n = (b + d) / 2)
    (h' : m' = ((a + 14) + (c - 2)) / 2 ∧ n' = ((b + 20) + (d - 4)) / 2) :
    Real.sqrt ((m - m') ^ 2 + (n - n') ^ 2) = 10 := by
  rcases h with ⟨hm, hn⟩
  rcases h' with ⟨hm', hn'⟩
  have eq1 : m' = m + 6 := by
    rw [hm', hm]
    ring
  have eq2 : n' = n + 8 := by
    rw [hn', hn]
    ring
  have eq3 : (m - m') ^ 2 + (n - n') ^ 2 = (10 : ℝ) ^ 2 := by
    rw [show m' = m + 6 by linarith [eq1], show n' = n + 8 by linarith [eq2]]
    nlinarith
  rw [eq3]
  exact Real.sqrt_sq (by norm_num)