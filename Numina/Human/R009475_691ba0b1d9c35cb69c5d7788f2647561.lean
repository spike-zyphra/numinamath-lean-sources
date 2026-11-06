import Mathlib

/- Let $a$ and $b$ be angles such that $\sin (a + b) = \frac{3}{4}$ and $\sin (a - b) = \frac{1}{2}.$  Find $\frac{\tan a}{\tan b}.$ -/
theorem calculus_11451 (a b : ℝ) (ha : Real.sin (a + b) = 3 / 4) (hb : Real.sin (a - b) = 1 / 2) :
    Real.tan a / Real.tan b = 5 := by
  have h1 : Real.sin a * Real.cos b + Real.cos a * Real.sin b = 3 / 4 := by
    linarith [ha, Real.sin_add a b]
  have h2 : Real.sin a * Real.cos b - Real.cos a * Real.sin b = 1 / 2 := by
    linarith [hb, Real.sin_sub a b]
  have h3 : Real.sin a * Real.cos b = 5 / 8 := by linarith
  have h4 : Real.cos a * Real.sin b = 1 / 8 := by linarith
  field_simp [Real.tan_eq_sin_div_cos]
  ring_nf
  linarith