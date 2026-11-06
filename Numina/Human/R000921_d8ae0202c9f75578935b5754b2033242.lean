import Mathlib

/- Suppose that $f$ is a function and $f^{-1}$ is the inverse of $f$.
If $f(1)=2$, $f(2) = 6$, and $f(3)=5$, then what is $f^{-1}(f^{-1}(6))$? -/
theorem algebra_19131 {f g : ℕ → ℕ} (hf : f 1 = 2 ∧ f 2 = 6 ∧ f 3 = 5)
  (f_has_inverse: f.HasLeftInverse ∧ f.HasRightInverse) (hg: g = f.invFun):
  g (g 6) = 1 := by
  -- f has inverse, so f⁻¹ must be injective
  have f_injective: Function.Injective f :=
    Function.HasLeftInverse.injective f_has_inverse.left
  -- so for any x, if f(x)=y, then g(y)=x
  have h1{x y:ℕ}(h: f x = y): g y = x := by
    rw [hg, ← h]
    apply f_injective
    apply Function.apply_invFun_apply
  -- since f(2)=6, so g(6)=2. f(1)=2, g(2)=1. therefore g(g(6))=g(2)=1
  rw [h1 hf.right.left, h1 hf.left]