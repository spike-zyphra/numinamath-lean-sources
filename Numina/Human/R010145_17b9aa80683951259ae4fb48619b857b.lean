import Mathlib

/- The first four terms of an arithmetic sequence are p, 9, 3p−q, and 3p+q. What is the 2010th term of this sequence?
(A) 8041
(B) 8043
(C) 8045
(D) 8047
(E) 8049
-/
theorem algebra_93930 (p q : ℝ) (h₁: 9 = p + d) (h₂: 3 * p - q = 9 + d)  (h₃: 3 * p + q = 3 * p - q + d) :
p + 2009 * d = 8041 := by
  -- compute d in terms of p, q using h3
  have hdpq : d = (3 * p + q) - (3 * p - q) := by linarith
  have hdq : d = 2 * q := by linarith
  rw [hdq] at h₁
  -- plug in d's value in other equations, in particular expressing p in terms of q
  have h₄: p = 9 - 2 * q := by linarith
  rw [hdq] at h₂
  rw [h₄] at h₂
  -- compute q by pluggin h4 in h2 and then using it compute p using h4
  have hq : q = 2 := by linarith
  have hp : p = 5 := by
    rw [hq] at h₄
    norm_num at h₄
    exact h₄
  rw [hp, hdq, hq]
  -- knowing p, q just compute
  norm_num