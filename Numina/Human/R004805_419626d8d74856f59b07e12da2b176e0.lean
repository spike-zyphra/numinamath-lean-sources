import Mathlib

open Real
/- 6. Given that $\alpha$ is an acute angle, vectors
$$
a=(\cos \alpha, \sin \alpha), b=(1,-1)
$$

satisfy $a \cdot b=\frac{2 \sqrt{2}}{3}$. Then $\sin \left(\alpha+\frac{5 \pi}{12}\right)=$ $\qquad$
-/
theorem algebra_328477 (α : ℝ) (ha : 0 < α ∧ α < π / 2) (h : Real.cos α * 1 + Real.sin α * -1 = 2 * Real.sqrt 2 / 3) :
    Real.sin (α + 5 * π / 12) = (2 + Real.sqrt 15) / 6 := by
  -- the dot product of $a$ and $b$ would be $\cos \alpha * 1 + \sin \alpha * (-1)$. So that's $\cos \alpha - \sin \alpha$. And it's given that this equals $\frac{2 \sqrt{2}}{3}$. So, the equation we have is: $\cos \alpha - \sin \alpha  = \frac{2 \sqrt{2}}{3}$.
  have h1 : Real.cos α - Real.sin α = 2 * Real.sqrt 2 / 3 := by
    rwa [mul_one, mul_neg_one, ← sub_eq_add_neg] at h
  --  Since $\alpha$ is an acute angle, both $\sin \alpha$ and $\cos \alpha$ are positive.
  have h2 : Real.cos α > 0 ∧ Real.sin α > 0 := by
    constructor
    · apply Real.cos_pos_of_mem_Ioo
      simp
      constructor
      all_goals linarith
    · apply Real.sin_pos_of_mem_Ioo
      simp
      constructor
      all_goals linarith
  -- $\cos \alpha - \sin \alpha$ can be written as $\sqrt{2} \cos (\alpha + \frac{\pi}{4})$.
  have h3 : Real.cos α - Real.sin α = Real.sqrt 2 * Real.cos (α + π / 4) := by
    simp [cos_add]
    rw [show √2 / 2 = 1 / √2 by field_simp]
    field_simp
  -- Then we know that $\cos (\alpha + \frac{\pi}{4}) = \frac{2}{3}$, which we can use to find $\sin (\alpha + \frac{\pi}{4})$.Since $\alpha + \frac{\pi}{4}$ is in the first quadrant, $\sin (\alpha + \frac{\pi}{4})$ is positive. So,$\sin (\alpha + \frac{\pi}{4})=\frac{\sqrt{5}}{3}$.
  have h4 : Real.cos (α + π / 4) = 2 / 3 ∧ Real.sin (α + π / 4) = Real.sqrt 5 / 3 := by
    rw [h1, mul_comm (a := 2), ← mul_div] at h3
    apply mul_left_cancel₀ (by norm_num) at h3
    simp [h3]
    suffices sin (α + π / 4) ^ 2 = (Real.sqrt 5 / 3) ^ 2  by
      rwa [sq_eq_sq₀] at this
      · simp [sin_add]
        apply add_nonneg
        all_goals simp
        all_goals linarith
      · positivity
    have := Real.sin_sq_add_cos_sq (α + π / 4)
    simp [← h3] at this
    rw [div_pow, sq_sqrt (by norm_num)]
    linarith
  -- $\sin (\alpha + \frac{5\pi}{12}) = \sin (\alpha + \frac{\pi}{4} + \frac{\pi}{6})$
  have h5 : Real.sin (α + 5 * π / 12) = Real.sin (α + π / 4 + π / 6) := by
    ring_nf
  -- Then, \sin (\alpha + \frac{\pi}{4} + \frac{\pi}{6}) = \sin (\alpha + \frac{\pi}{4}) \cos \frac{\pi}{6} + \cos (\alpha + \frac{\pi}{4}) \sin \frac{\pi}{6} = \frac{\sqrt{5}}{3}\frac{\sqrt{3}}{2}+ \frac{2}{3}\frac{1}{2} = \dfrac{2 + \sqrt{15}}{6}.
  rw [h5, Real.sin_add, h4.1, h4.2]
  field_simp
  rw [← sqrt_mul (by norm_num)]
  ring_nf