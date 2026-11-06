import Mathlib

open Real

/-If $f(x) = \frac{4x+1}{3}$ what is the value of $\left[f^{-1}(1)\right]^{-1}$?-/
theorem algebra_20182 {f : ℝ → ℝ} (hf : f = fun x => (4 * x + 1) / 3) :
    (f ⁻¹' {1})⁻¹ = {2} := by
  ext x
  simp [hf]
  apply Iff.intro <;> intro h
  -- show that x = 2
  . field_simp at h
    replace h : 4 / x = 2 := by linarith only [h]
    calc
      x = 2 * (1 / 2) * x := by ring_nf
      _ = (4 / x) * (1 / 2) * x := by rw [h]
      _ = 2 := by ring_nf; rw [mul_inv_cancel₀]; norm_num; intro h0; rw [h0] at h; norm_num at h
  -- show that x = 2 is the only solution
  . rw [h]
    norm_num