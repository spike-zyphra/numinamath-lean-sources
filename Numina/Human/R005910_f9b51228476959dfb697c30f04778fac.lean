import Mathlib

/- A real number $x$ satisfies $9^{x}+3^{x}=6$. Compute the value of $16^{1 / x}+4^{1 / x}$.-/
theorem algebra_610673 (x : ℝ) (h₀ : (9 : ℝ) ^ x + (3 : ℝ) ^ x = 6) : (16 : ℝ) ^ (1 / x) + (4 : ℝ) ^ (1 / x) = 90 := by
  -- Show that (3^x + 1/2)^2 = 25/4.
  have h₁ : ((3 : ℝ) ^ x + 1 / 2) ^ 2 = (5 / 2) ^ 2 := by
    ring_nf
    rw [<-Real.rpow_natCast, <-Real.rpow_mul, mul_comm, Real.rpow_mul]
    norm_num
    linarith only [h₀]
    norm_num
    norm_num
  -- Show that 3^x + 1/2 = 5/2.
  rw [sq_eq_sq₀ (by positivity) (by norm_num)] at h₁
  apply eq_sub_of_add_eq at h₁
  norm_num at h₁
  -- Show that 3 = 2 ^ (1 / x).
  replace h₁ : 3 = (2 : ℝ) ^ (1 / x) := by
    rw [<-h₁, <-Real.rpow_mul, mul_one_div, div_self]
    norm_num
    by_contra!
    simp [this] at h₁
    norm_num
  -- Calculate the sum using the previous result.
  rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
  iterate 2 rw [<-Real.rpow_mul]
  rw [mul_comm]
  nth_rw 2 [mul_comm]
  iterate 2 rw [Real.rpow_mul]
  rw [<-h₁]
  all_goals
    norm_num
