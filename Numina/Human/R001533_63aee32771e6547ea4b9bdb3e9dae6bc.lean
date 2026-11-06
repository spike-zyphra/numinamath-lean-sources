import Mathlib

/- 3. (HUN) Let $x$ be an angle and let the real numbers $a, b, c, \cos x$ satisfy the following equation:  $$ a \cos ^{2} x+b \cos x+c=0 . $$  Write the analogous quadratic equation for $a, b, c, \cos 2 x$. Compare the given and the obtained equality for $a=4, b=2, c=-1$.  Second Day -/
open Real in
theorem algebra_24473 {x : ℝ} (a b c : ℝ) (h : a * Real.cos x ^ 2 + b * Real.cos x + c = 0): 
    (a^2) * (cos (2 * x))^2 + (2 * a^2 + 4 * a * c - 2 * b^2) * cos (2 * x) + 
    a^2 + 4 * a * c - 2 * b^2 + 4 * c^2 = 0 := by 
  apply_fun (· * 4 * (a * (cos x)^2 - b * cos x + c)) at h 
  ring_nf at h 
  convert h using 1 
  rw [mul_comm 4 (c^2)]
  rw [cos_sq, cos_sq]
  ring_nf 
  congr 2
  rw [add_assoc (a * c * 4 + a * c * cos (x * 2) * 4), add_assoc, 
    add_right_inj (a * c * 4 + a * c * cos (x * 2) * 4)]
  conv_rhs => 
    enter [1, 2]; rw [show 4 = 2 * 2 by norm_num, pow_mul, cos_sq]
    ring_nf; rw [cos_sq]; ring_nf
  ring