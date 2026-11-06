import Mathlib

/- 2.164. $\frac{x^{2}+2 x-3+(x+1) \sqrt{x^{2}-9}}{x^{2}-2 x-3+(x-1) \sqrt{x^{2}-9}} ; x>3$. -/
theorem algebra_159092 {x : ℝ} (hx : x > 3) :
    ((x ^ 2 + 2 * x - 3 + (x + 1) * Real.sqrt (x ^ 2 - 9)) /
     (x ^ 2 - 2 * x - 3 + (x - 1) * Real.sqrt (x ^ 2 - 9))) =
    Real.sqrt ((x + 3) / (x - 3)) := by
    -- first prove √(x-3) and √(x+3) are positive as that'll be useful later
    have hsqrt_pos : √(x-3) > 0 ∧ √(x+3) > 0 := by
          constructor
          repeat
            apply Real.sqrt_pos.mpr
            linarith
    -- now do algebraci manipulation, write x-3, x+3 as square root multiplications and factor them out then cancel common parts
    calc
      (x ^ 2 + 2 * x - 3 + (x + 1) * √(x ^ 2 - 9)) / (x ^ 2 - 2 * x - 3 + (x - 1) * √(x ^ 2 - 9)) = ((x+3)*(x-1) + (x+1) * √(x^2-9))/((x-3)*(x+1) + (x-1) * √(x^2-9)) := by ring_nf
      _ = ((x+3)*(x-1) + (x+1) * √(x-3) * √(x+3))/((x-3)*(x+1) + (x-1) * √(x-3) * √(x+3)) := by
        have : x^2 - 9 = (x-3) * (x+3) := by ring
        rw [this, Real.sqrt_mul]
        ring_nf
        linarith
      _ = (√(x+3) * ((x-1) * √(x+3) + (x+1) * √(x-3))) / (√(x-3) * ((x-1) * √(x+3) + (x+1) * √(x-3))) := by
        nth_rw 1 [← Real.mul_self_sqrt (by linarith: 0 ≤ x+3)]
        nth_rw 2 [← Real.mul_self_sqrt (by linarith: 0 ≤ x-3)]
        ring_nf
      _ = √(x + 3) / √(x - 3) := by
        have : (x-1) * √(x+3) + (x+1) * √(x-3) > 0 := by
          apply Right.add_pos' <;> apply mul_pos <;> linarith
        have : √(x-3) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith
        field_simp
        ring_nf
      _ = √((x + 3) / (x - 3)) := by
        rw [Real.sqrt_div]
        linarith