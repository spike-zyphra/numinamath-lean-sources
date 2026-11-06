import Mathlib

open Real

/-Let $t(x) = \sqrt{3x+1}$ and $f(x)=5-t(x)$. What is $t(f(5))$?-/
theorem algebra_11493 {t f : ℝ → ℝ}
    (ht : t = fun x => sqrt (3 * x + 1)) (hf : f = fun x => 5 - t x) :
    t (f 5) = 2 := by 
  -- calculate f 5 = 1
  have eq1 : f 5 = 1 := by
    calc
      f 5 = 5 - sqrt (3 * 5 + 1) := by rw[hf, ht]
      _ = 5 - sqrt (4 * 4) := by norm_num
      _ = 5 - |4| := by rw [Real.sqrt_mul_self_eq_abs 4]
      _ = 1 := by norm_num
  
  --calculate t (f 5) = 2
  calc
    t (f 5) = t 1 := by rw [eq1] 
    _ = sqrt (3 * 1 + 1) := by rw [ht]
    _ = sqrt (2 * 2) := by norm_num
    _ = 2 := by rw [Real.sqrt_mul_self_eq_abs 2]; norm_num
