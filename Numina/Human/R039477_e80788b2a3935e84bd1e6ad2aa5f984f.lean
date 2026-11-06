import Mathlib

/- Let $f(x) = \sqrt{x}$ and $g(x) = x^2.$ Find $f(g(f(g(f(8))))).$ -/
theorem algebra_22020 {f g : ℝ → ℝ} (hf : f = Real.sqrt) (hg : g = fun x => x ^ 2) :
    f (g (f (g (f 8)))) = 2 * Real.sqrt 2 := by 
  rw [hg, hf]
  simp only [Function.comp_apply, hg, hf]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> ring_nf <;> norm_num