import Mathlib

open Real

/- ## Problem Statement

Calculate the definite integral:


$$

\int_{0}^{4} e^{\sqrt{(4-x) /(4+x)}} \cdot \frac{d x}{(4+x) \sqrt{16-x^{2}}}

$$
 -/
theorem calculus_128020 : ∫ x in (0)..4, exp (sqrt ((4 - x) / (4 + x))) / ((4 + x) * sqrt (16 - x ^ 2)) = (exp 1 - 1) / 4 := by
  -- Define g(x) = √((4 - x) / (4 + x)).
  set g : ℝ → ℝ := fun x => √((4 - x) / (4 + x))
  -- Define f(x) = exp(g(x)) / ((4 + x) * √(16 - x^2)).
  set f : ℝ → ℝ := fun x => exp (g x) / ((4 + x) * √(16 - x^2))
  -- Define F(x) = (-1 / 4) * exp(g(x)).
  set F : ℝ → ℝ := fun x => (-1 / 4) * exp (g x)
  -- Prove that F is continuous on [0, 4].
  have hF : ContinuousOn F (Set.Icc 0 4) := by
    dsimp [F, g]
    apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.rexp
    apply ContinuousOn.sqrt
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    simp only [Set.mem_Icc] at hx
    linarith
  -- Prove that the derivative of F(x) is f(x) for all x in (0, 4).
  have hdf x (hx : x ∈ Set.Ioo 0 4) : HasDerivAt F (f x) x := by
    simp only [Set.mem_Ioo] at hx
    -- Show that f(x) = (-1 / 4) * (exp (g x) * ((-1 * (4 + x) - (4 - x) * 1) / (4 + x)^2 / (2 * √((4 - x) / (4 + x))))).
    have eq : f x = (-1 / 4) * (exp (g x) * ((-1 * (4 + x) - (4 - x) * 1) / (4 + x)^2 / (2 * √((4 - x) / (4 + x))))) := by
      ring_nf
      rw [mul_assoc, ← mul_inv]
      congr
      symm
      calc
        (16 + x * 8 + x^2) * √(-(x * (4 + x)⁻¹) + (4 + x)⁻¹ * 4) = (x + 4) ^ 2 * √((4 - x) / (4 + x)) := by
          ring_nf
        _ = (x + 4) * √(((x + 4) * (x + 4)) * ((4 - x) / (4 + x))) := by
          rw [← pow_two, sqrt_mul (by positivity), sqrt_sq (by linarith)]
          ring
        _ = (x + 4) * √(16 - x^2) := by
          congr
          field_simp [show 4 + x ≠ 0 by linarith]
          ring
        _ = x * √(16 - x^2) + √(16 - x^2) * 4 := by ring
    rw [eq]
    -- The result follows from basic properties of derivatives.
    apply HasDerivAt.const_mul
    apply HasDerivAt.exp
    apply HasDerivAt.sqrt
    · apply HasDerivAt.div
      · apply HasDerivAt.const_sub
        exact hasDerivAt_id' x
      · apply HasDerivAt.const_add
        exact hasDerivAt_id' x
      · linarith
    · field_simp
      constructor <;> linarith
  -- Apply the Fundamental theorem of Calculus to f(x) = F'(x).
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hF hdf]
  -- The integral from the theorem statement is equal to F(4) - F(0)
  --   = (-1/4) * exp(g(4)) + 1/4 * exp(g(0))
  --   = (-1/4) * exp(0) + 1/4 * exp(1)
  --   = (exp(1) - 1) / 4.
  · simp [F, g]
    ring
  -- It is left to show that f is integrable on [0, 4].
  -- f(x) = F'(x). To show that f is integrable, it is enough to show that
  -- 0 ≤ f(x) for all x ∈ (0, 4).
  · apply intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := F)
    · rw [show Set.uIcc (0 : ℝ) 4 = Set.Icc 0 4 by simp]
      exact hF
    · rw [show min (0 : ℝ) 4 = 0 by norm_num, show max (0 : ℝ) 4 = 4 by norm_num]
      exact hdf
    · simp
      intro x hx1 hx2
      positivity