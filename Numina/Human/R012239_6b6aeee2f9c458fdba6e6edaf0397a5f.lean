import Mathlib
open Real

/- If (a+1/a)^2=3, then a^3=1/(a^3) equals:
(A) (10√3)/3 (B) 3√3 (C) 0 (D) 7√7 (E) 6√3 -/
theorem algebra_95549 {a : ℝ} (ha : a ≠ 0) (h : (a + 1 / a) ^ 2 = 3) : a ^ 3 + 1 / a ^ 3 = 0 := by
  rw [← sq_sqrt (by norm_num:(0:ℝ) ≤ 3)] at h
  by_cases haa:(0 ≤ a + 1 / a)
  -- discuss the sign of a+1/a
  · rw [pow_left_inj₀ haa (by norm_num) (by norm_num)] at h
    have h':=h
    rw [← pow_left_inj₀ haa (by norm_num:0≤√3) (by norm_num:3≠0)] at h
    -- obtain the expanded expression of (a+1/a)^3
    have h1:a*(a*a)+(1/a)^3+3*(a*(a*(1/a))+(1/a)*(a*(1/a)))=(√3*√3)*√3:=by linarith
    -- substitude the value of a+1/a into the equation to obtain the result
    simp [ha] at h1 h'
    rw [h'] at h1
    simp [pow_three] at *
    assumption
  · have ha':=le_of_lt $ lt_of_not_le haa
    rw [(by norm_num:(0:ℝ)=-0),le_neg,neg_add] at ha'
    have h':(-a + -(1 / a)) ^ 2 = √3 ^ 2 := by linarith
    rw [pow_left_inj₀ ha' (by norm_num) (by norm_num)] at h'
    have h'':=h'
    rw [← pow_left_inj₀ ha' (by norm_num:0≤√3) (by norm_num:3≠0)] at h'
    -- obtain the expanded expression of (-a-1/a)^3
    have h1:(-a)*((-a)*(-a))+(-(1/a))^3+3*((-a)*((-a)*(-(1/a)))+(-(1/a))*((-a)*(-(1/a))))=(√3*√3) *√3:=by linarith
    -- substitude the value of -a-1/a into the equation to obtain the result
    simp [ha] at h1 h''
    rw [h''] at h1
    simp [pow_three] at *
    linarith