import Mathlib

/- 413. Prove that if $a^{2}+b^{2}=7 a b$, then


$$

\log _{k} \frac{a+b}{3}=\frac{1}{2}\left(\log _{k} a+\log _{k} b\right)

$$


where


$$

a>0, b>0, k>0, k \neq 1

$$
 -/
theorem algebra_278208 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℝ) (hk : 0 < k ∧ k ≠ 1)
    (h : a^2 + b^2 = 7 * a * b) :
    Real.logb k ((a + b) / 3) = (Real.logb k a + Real.logb k b) / 2 := by
  -- let's add 2*a*b on both sides of assumption
  apply congr_arg (fun x => x+2*a*b) at h
  have h' : (((a+b)/3))^2 = a * b := by ring_nf at h ⊢; apply congr_arg (fun x => x/9) at h; ring_nf at h ⊢; assumption
  -- then taking log of both sides gives conclusion
  apply congr_arg (fun x=> Real.logb k x) at h'
  calc Real.logb k ((a + b) / 3)
  _ = (2 * Real.logb k ((a + b) / 3)) / 2 := by ring_nf
  _ = (Real.logb k (((a + b) / 3)^2)) / 2 := by rw [← Real.logb_rpow_eq_mul_logb_of_pos (by linarith) ]; simp
  _ = (Real.logb k (a * b)) / 2 := by rw [h']
  _ = (Real.logb k a + Real.logb k b) / 2 := by rw [Real.logb_mul (by apply ne_of_gt; assumption) (by apply ne_of_gt; assumption)]