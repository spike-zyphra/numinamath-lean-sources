import Mathlib

/-Find $\frac{\frac{1}{3} + \frac{1}{4}}{ \frac{2}{5} - \frac{1}{6}}$. Express your answer as a fraction in simplest form.-/
theorem algebra_15391 : (1/3 + 1/4) / (2/5 - 1/6) = (5/2 : ℝ ) ∧ (2).gcd 5 = 1 := by 
  -- verify that $\frac{\frac{1}{3} + \frac{1}{4}}{ \frac{2}{5} - \frac{1}{6}}$ = $\frac 5 2$
  field_simp
  ring_nf
  -- prove that 5 / 2 is simplest form.
  simp
  exact Nat.odd_iff.mpr rfl