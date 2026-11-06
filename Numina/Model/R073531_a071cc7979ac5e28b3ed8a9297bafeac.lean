import Mathlib

theorem algebra_195118 {p q : ℝ} (h1 : p * 1 ^ 2 + q + 1 = 869) (h2 : p * 2 ^ 3 + q + 1 = 883)
    (hd : p * 2 ^ 9 + q + 1 = d) : d = 1891 := by 
  have eq1 : p + q = 868 := by 
    linarith
  have eq2 : 8 * p + q = 882 := by 
    linarith
  have hp : p = 2 := by 
    linarith [eq1, eq2]
  have hq : q = 866 := by 
    linarith [eq1, hp]
  have : p * 2 ^ 9 + q + 1 = 1891 := by
    rw [hp, hq]
    norm_num
  linarith [hd, this]