import Mathlib

theorem algebra_10183 {f g : ℝ → ℝ} (hf : f = fun x => 5 * x ^ 2 - 1 / x + 3)
    (hg : g = fun x => x ^ 2 - k) (hfg : f 2 - g 2 = 2) :
    k = -33 / 2 := by
  have eq1 : f 2 = 5 * (2 : ℝ) ^ 2 - 1 / (2 : ℝ) + 3 := by
    rw [hf]
  have eq2 : g 2 = (2 : ℝ) ^ 2 - k := by 
    rw [hg]
  rw [eq1, eq2] at hfg
  norm_num at hfg
  linarith