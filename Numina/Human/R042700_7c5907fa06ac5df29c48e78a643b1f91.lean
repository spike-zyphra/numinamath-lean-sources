import Mathlib
open Real


/-Suppose that |x + y|+|x - y| = 2. What is the maximum possible value of x^2 - 6x + y?
(A) 5 (B) 6 (C)7 (D) 8 (E) 9-/
theorem algebra_94581 (x y : ℝ) (h : abs (x + y) + abs (x - y) = 2) :
x ^ 2 - 6 * x + y ^ 2 ≤ 8 := by
-- prove a nonlinear inequality lemma that is useful for the main proof
have hl:∀ k:ℝ,0≤1+k→k≤1→k^2≤1 := by
  intros k hk1 hk2
  rw [← sub_le_sub_iff_right 1] at hk1;simp at hk1
  rw [(by simp:k=-(-k)),← le_neg] at hk1;simp at hk1
  by_cases hk0:0≤k
  · have hkk:=pow_le_pow_left₀ hk0 hk2 2
    rw [(by simp:(1:ℝ)^2=1)] at hkk
    exact hkk
  · simp at hk0
    have hk01:=le_of_lt hk0
    rw [(by simp:(0:ℝ)=-(-0)),← le_neg,(by simp:(-0:ℝ)=0)] at hk01
    have hkk:=pow_le_pow_left₀ hk01 hk1 2
    rw [(by simp:(-k)^2=k^2),(by simp:(1:ℝ)^2=1)] at hkk
    exact hkk
-- discussing the sign of x and y and the sign of the absolute values respectively
-- obtaining the range of x ^ 2 - 6 * x + y ^ 2 for each case and combining the result
cases' le_total 0 (x+y) with h1 h1
· simp [abs_of_nonneg,abs_of_nonpos,h1] at h
  cases' le_total 0 (x-y) with h2 h2
  · simp [abs_of_nonneg,abs_of_nonpos,h2] at h
    ring_nf at h;simp at h;subst h;simp at h2;simp
    linarith [hl y h1 h2]
  · simp [abs_of_nonneg,abs_of_nonpos,h2] at h
    ring_nf at h;simp at h;subst h;simp at h2;simp
    rw [add_comm] at h1
    linarith [hl x h1 h2]
· cases' le_total 0 (x-y) with h2 h2
  · simp [abs_of_nonneg,abs_of_nonpos,h1,h2] at h
    simp [abs_of_nonneg,abs_of_nonpos,h1] at h2
    ring_nf at h;have hy:y=-1:=by linarith
    subst hy;simp at h;simp
    linarith [hl x (by linarith:0≤1+x) (by linarith:x≤1)]
  · simp [abs_of_nonneg,abs_of_nonpos,h1,h2] at h
    simp [abs_of_nonneg,abs_of_nonpos,h1] at h2
    ring_nf at h;have hx:x=-1:=by linarith
    subst hx;simp at h;simp
    linarith [hl y (by linarith:0≤1+y) (by linarith:y≤1)]