import Mathlib

/-Rationalize the denominator of $\frac{\sqrt{32}}{\sqrt{16}-\sqrt{2}}$. The answer can be written as $\frac{A\sqrt{B}+C}{D}$, where $A$, $B$, $C$, and $D$ are integers, $D$ is positive, and $B$ is not divisible by the square of any prime.  Find the minimum possible value of $A+B+C+D$.-/
theorem algebra_12788 : √32/(√16 - √2) = (8 * √2 + 4)/7 ∧ 8 + 2 + 4 + 7 = 21 := by
  constructor
  case right
  . -- 8 + 2 + 4 + 7 = 21
    linarith
  have : √16 = 4 := by
    have : (16 : ℝ) = 4^2 := by linarith
    rw [this, Real.sqrt_sq]
    linarith
  rw [this]
  have : √32 * (4 + √2) / ((4 - √2) * (4 + √2)) = √32 / (4 - √2) := by
    rw [←div_div, div_right_comm, ←mul_div, div_self, mul_one]
    have : 0 < √2 := by refine Real.sqrt_pos_of_pos (by linarith)
    linarith
  rw [this.symm]
  have : (4 - √2) * (4 + √2) = 14 := by
    ring_nf
    rw [Real.sq_sqrt]
    repeat linarith
  rw [this, mul_add]
  have : √32 = 4 * √2 := by
    have : (32 : ℝ) = 4^2 * 2 := by linarith
    rw [this, Real.sqrt_mul, Real.sqrt_sq]
    repeat linarith
  rw [this, mul_assoc 4 √2 √2, Real.mul_self_sqrt (by linarith)]
  ring_nf
