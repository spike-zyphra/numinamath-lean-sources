import Mathlib

/- Given the function $f(x) = 3x^{a-2} - 2$ passes through the point $(2, 4)$, find the value of $a$. -/
theorem algebra_9018 {f : ℝ → ℝ}{a:ℝ}(hf : f = fun x => 3 * x ^ (a - 2) - 2) (ha : f 2 = 4) : a = 3 := by
rw [hf] at ha
simp at ha
-- substitute point (2,4) back into the funtion, we get 3*(2^(a-2))-2=4
-- simplify, we get 2^(a-2) = 2
-- since exponential function f(x)=2^x is injective, we get a-2=2.
-- theorem f(x)=log x is injective is already in mathlib, so we use the injectivity of logx, and take log of both sides, instead of proving 2^x is injective.
have h1: (2:ℝ)^(a-2:ℝ) = 2 := by
  have ht1:  3 * 2 ^ (a - 2:ℝ) = (6:ℝ) := by
    have: 6 = (4:ℝ) + 2 := by norm_num
    rw [this]
    rw [← ha]
    simp
  have: (6:ℝ) = 3 * 2 := by norm_num
  rw [this] at ht1
  have: (2:ℝ) ^ (a - 2:ℝ) = 2 ∨ (3:ℝ) = 0 := by
    apply mul_eq_mul_left_iff.mp ht1
  rcases this with hl | hr
  exact hl
  norm_num at hr
have: (2:ℝ) = Real.exp (Real.log 2) := by
  have: 0 < (2:ℝ) := by norm_num
  symm
  apply Real.exp_log this
nth_rewrite 3 [this] at h1
have h2: (a-2:ℝ) = (1:ℝ) := by
  have: (2:ℝ)^(a-2:ℝ) = Real.exp (Real.log 2 * (a-2:ℝ)) := by
    have: 0 < (2:ℝ) := by norm_num
    exact Real.rpow_def_of_pos this (a - 2:ℝ)
  rw [this] at h1
  have ht1: Real.log 2 * (a - 2:ℝ) = Real.log 2 := Real.exp_eq_exp.mp h1
  nth_rw 2 [← mul_one (Real.log 2)] at ht1
  have: Real.log 2 ≠ 0 := by
    have h11: 0 < (2:ℝ) := by norm_num
    have h22: 1 ≠ (2:ℝ) := by norm_num
    exact Real.log_ne_zero_of_pos_of_ne_one h11 (id (Ne.symm h22))
  have h2: (a-2:ℝ) = 1 ∨ Real.log 2 = 0 := by
    apply mul_eq_mul_left_iff.mp ht1
  rcases h2 with h2l | h2r
  exact h2l
  contradiction
have h3: (a:ℝ) = 3 := by
  have: (3:ℝ) = 1+2 := by norm_num
  rw [this, ← h2]
  ring
exact h3