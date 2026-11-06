import Mathlib
open Real

/-Determine the value of ab if log_8 a + log_4 (b^2)=5 and log_8 b+log_4 a^2=7.-/

theorem AIME_Algebra_20549 {a b : Real} (ha : 0 < a) (hb : 0 < b)
(h1 : Real.logb 8 a + Real.logb 4 (b ^ 2) = 5) (h2 : Real.logb 8 b + Real.logb 4 (a ^ 2) = 7) :a * b = 512 := by 
--We simpify the condition h1 and h2
  simp only [logb] at h1 h2
  rw[log_pow] at h1 h2
--We prove the identity by prove that they are the same after taking log.
  have h:=log_injOn_pos
  simp only [Set.InjOn] at h
  apply h
  simp only [Set.mem_Ioi]
  apply mul_pos ha hb
  norm_num
--Our goal is a linear equation about log a and log b with coefficients in ℝ[ log 2]
  rw[log_mul]
  field_simp at h1 h2
  have aux:log 4=(2:Real)*log 2∧log 8=(3:Real)*log 2∧ log 512=(9:Real)*log 2:=by
    split_ands
    all_goals
    rw[←Nat.cast_eq_ofNat,←Nat.cast_eq_ofNat,←log_pow]
    norm_num
  rw[aux.1,aux.2.1] at h1
  rw[aux.1,aux.2.1] at h2
  rw[aux.2.2]
  ring_nf at h1 h2
--We clear the square of log 2 to make both h1 and h2 linear equations on log a, log b and log 2.
  rw[pow_two,mul_assoc,mul_comm,mul_assoc,mul_assoc,mul_assoc,←mul_add,mul_right_inj'] at h1 h2
--We solve the linear equation.
  linarith
--We check the conditions.
  apply ne_of_gt (log_pos (by norm_num))
  apply ne_of_gt (log_pos (by norm_num))
  linarith
  linarith