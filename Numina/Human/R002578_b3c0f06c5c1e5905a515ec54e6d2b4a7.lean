import Mathlib

open Real
/-For all integers n greater than 1, define a_n=1/(log_n 2002). Let b=a_2+a_3+a_4+a_5 and c=a_10+a_11+a_12+a_13+a_14. Then b−c equals (A) −2(B) −1(C)1/2002(D)1/1001 ​(E) 1/2
-/
theorem AMC_Algebra_95686 {a : ℕ → ℝ} (ha : ∀ n, 1 < n → a n = 1 / logb n 2002) (b c : ℝ) (hb : b = a 2 + a 3 + a 4 + a 5) (hc : c = a 10 + a 11 + a 12 + a 13 + a 14) :
b - c = -1 := by 
--We translate the definition of a_n into a_n=1/(log 2002/log n)
  simp only [Real.logb] at ha
--Simplify the definition of a_n.
  norm_num at ha
--Substitute b,c and the definition of a_n
  rw[hb,hc]
  rw[ha,ha,ha,ha,ha,ha,ha,ha,ha]
  field_simp
--It suffices to prove the following identiy. We prove it by using log x +log y= log xy and log x - log y=log x/y.
  rw[←log_mul,←log_mul,←log_mul,←log_mul,←log_mul,←log_mul,←log_mul]
  norm_num
  rw[←sub_eq_zero,sub_neg_eq_add,←log_div,←log_mul]
--We check assumptions are satisfied.
  all_goals norm_num