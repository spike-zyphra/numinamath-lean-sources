import Mathlib

/- Given the function $f(x) = f'\left(\frac{\pi}{6}\right)\sin x + \cos x$, find the value of $f\left(\frac{\pi}{6}\right)$.-/
theorem algebra_9236 {f : ℝ → ℝ}
    (hf : ∀ x, f x = deriv f (Real.pi / 6) * Real.sin x + Real.cos x) :
    f (Real.pi / 6) = -1 := by
  set ξ : ℝ := deriv f (Real.pi / 6) with hξ
  -- Calculating $f'(x)=\xi\cos x - \sin x$.
  have derivf : ∀ x, deriv f x = ξ * Real.cos x - Real.sin x := by
    intro x
    rw [show f = fun x => f x from rfl]
    simp [hf]
    simpa using by ring
  -- Substitute $x=\pi/6$ to the deriv of $f(x)$.
  have := derivf (Real.pi / 6)
  rw [← hξ, Real.cos_pi_div_six, Real.sin_pi_div_six] at this
  field_simp at this
  have : (2 - √3) * ξ = -1 := by linear_combination this
  apply_fun ((2 + √3) * ·) at this
  rw [← mul_assoc, ← sq_sub_sq, Real.sq_sqrt (by norm_num)] at this
  -- Solve that $\xi=-2-\sqrt{3}$.
  norm_num at this
  rw [hf, Real.cos_pi_div_six, Real.sin_pi_div_six, this]
  -- Hence, $f(\pi/6)=-1$.
  ring
