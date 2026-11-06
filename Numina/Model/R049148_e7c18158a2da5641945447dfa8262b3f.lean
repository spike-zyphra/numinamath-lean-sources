import Mathlib

theorem algebra_257114 {r s : ℝ} (hr : (1984 * r) ^ 2 - 1983 * 1985 * r - 1 = 0)
    (hs : 1983 * s ^ 2 - 1984 * s + 1 = 0) (hroots : r > s) :
    r - s = 1982 / 1983 := by
  have hr1 : r = 1 := by
    nlinarith [sq_nonneg (1984 * r - 1984), sq_nonneg (1984 * r + 1), sq_nonneg (r - 1), sq_nonneg (1984 * r)]
  have hs1 : s = 1 / 1983 := by
    have h1 : 1983 * s ^ 2 - 1984 * s + 1 = 0 := by linarith
    have h2 : (s - 1 / 1983) * (1983 * s - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- s - 1/1983 = 0
      linarith
    · -- 1983s - 1 = 0
      linarith
  rw [hr1, hs1]
  all_goals norm_num