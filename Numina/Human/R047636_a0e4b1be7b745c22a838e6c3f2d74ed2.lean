import Mathlib

/-Simplify $\frac{\sqrt{40\cdot9}}{\sqrt{49}}$.-/
theorem algebra_20434 : Real.sqrt (40 * 9) / Real.sqrt 49 = 6 * Real.sqrt 10 / 7 := by
    --Factoring the squares out of $40\cdot9$ gives us $2^2\cdot3^2\cdot10 = 6^2\cdot10$.  Thus, the numerator is $6\sqrt{10}$.
    have  hc : √(40 * 9) =  √40 * √9  := by
      rw[Real.sqrt_mul]
      linarith
    have sqrt9_eq_3 : √9 = 3 := by
      rw [Real.sqrt_eq_cases]
      simp
      ring_nf
    --The denominator is $7$, because $7^2=49$.  So our answer is $\boxed{\frac{6\sqrt{10}}{7}}$.
    have sqrt49_eq_7 : √49 = 7 := by
      rw [Real.sqrt_eq_cases]
      simp
      ring_nf
    rw [sqrt49_eq_7]
    rw [hc]
    rw [show (40 : ℝ ) = (4 * 10) by ring_nf]
    have  hc2 : √(4 * 10) =  √4 * √10  := by
      rw[Real.sqrt_mul]
      linarith
    rw [hc2]
    have sqrt4_eq_2 : √4 = 2 := by
      rw [Real.sqrt_eq_cases]
      simp
      ring_nf
    rw[sqrt9_eq_3] ; rw [sqrt4_eq_2]
    ring_nf