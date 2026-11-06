import Mathlib

theorem algebra_21221 {n : ℕ} (hn : Even n) (h : (n + 2) ^ 2 - n ^ 2 = 268) : (n + 2) ^ 2 = 4624 := by
  have eq1 : (n + 2) ^ 2 = n ^ 2 + 268 := by
    omega
  have eq2 : 4 * n + 4 = 268 := by
    nlinarith [eq1]
  have eq3 : 4 * n = 264 := by
    omega
  have eq4 : n = 66 := by
    omega
  calc
    (n + 2) ^ 2 = (66 + 2) ^ 2 := by rw [eq4]
    _ = 68 ^ 2 := by norm_num
    _ = 4624 := by norm_num