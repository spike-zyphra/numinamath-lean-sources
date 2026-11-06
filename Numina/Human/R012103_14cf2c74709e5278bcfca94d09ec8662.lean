import Mathlib

open Real
/-
$8.58 \log _{4} x+\log _{2}(\sqrt{x}-1)<\log _{2} \log _{\sqrt{5}} 5$ (find integer values of $x$).
-/

theorem inequalities_180349 (x: ℤ) (h1: 0 < x) (h2: 0 ≤ x) (h3: 0 < √x - 1):
(logb 4 x + logb 2 (√x - 1) < logb 2 (logb (√5) 5)) ↔ (x = 2 ∨ x = 3) := by

  --We first simplify our assumption a little.
  --By using the properties of log, we get that the assumption is equivalent to √↑x * (√↑x - 1) < 2
  have : 0 < (x:ℝ) := by norm_cast

  have eq: (logb (√5) 5) = 2 := by 
    have : 5 = (√5)^2 := by norm_num
    nth_rw 2 [this]
    simp only [Real.logb_pow]
    have : 1 < √5 := by refine lt_sqrt_of_sq_lt ?_; norm_num
    simp [this]
  rw [eq]

  nth_rw 1 [← log_div_log]
  have : (4:ℝ) = 2^2 := by norm_num
  rw [this]
  rw [log_pow]
  have : log ↑x / (@Nat.cast ℝ instNatCast 2 * log 2) = logb 2 (√x) := by
    field_simp
    have : √x = x^((1:ℝ)/2) := by exact sqrt_eq_rpow ↑x
    rw [this]
    rw [Real.logb_rpow_eq_mul_logb_of_pos]
    rw [← log_div_log]
    field_simp
    linarith
  rw [this]
  have : logb 2 √↑x + logb 2 (√↑x - 1) = logb 2 ((√x)*(√x-1)) := by rw [Real.logb_mul]; linarith; linarith
  rw [this]
  rw [Real.logb_lt_logb_iff]
  


  constructor
  
  --From left to right. We solve this quadratic equation for √x.
  intro h
  have xl: 1 < x := by 
    by_contra 
    have xle1 : x ≤ 1 := by linarith
    have : √x ≤ 1 := by refine sqrt_le_one.mpr ?_; norm_cast
    nlinarith
  have xu: x < 4 := by 
    by_contra 
    have xge4 : 4 ≤ x := by linarith
    have : 2 ≤ √x := by refine (le_sqrt' ?_).mpr ?_; linarith; norm_num; norm_cast
    nlinarith
  omega

  --From right to left. Simple verification.
  intro h
  rcases h with xe | xe
  
  rw [xe]
  norm_num
  have : √2 - 1 < √ 2:= by norm_num
  have : √2 * √2 = 2:= by norm_num
  nth_rw 3 [← this] 
  have : 0 < √ 2 := by positivity
  nlinarith

  rw [xe]
  norm_num
  have : 0 < √ 3 := by positivity
  have : √3 < 2 := by refine (sqrt_lt' ?_).mpr ?_; norm_num; norm_num
  have : √3 - 1 < 1 := by linarith
  have : √3 * 1 < 2 := by norm_num; linarith
  nlinarith
  linarith
  nlinarith
  norm_num
    