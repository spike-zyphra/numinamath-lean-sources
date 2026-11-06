import Mathlib

/- Suppose that $h(x)=f^{-1}(x)$. If $h(2)=10$, $h(10)=1$ and $h(1)=2$, what is $f(f(10))$? -/
theorem algebra_20345 {f h : ℝ → ℝ} (hf : Function.RightInverse h f)
    (h2 : h 2 = 10) (h10 : h 10 = 1) (h1 : h 1 = 2) :
    f (f 10) = 1 := by
  -- $f(f^{-1}(2))=2$
  have eq1 := hf 2
  -- So $f(10)=f(f^{-1}(2))=2$
  rw [h2] at eq1
  -- $f(f^{-1}(1))=1$
  have eq2 := hf 1
  -- So $f(2)=f(f^{-1}(1))=1$
  rw [h1] at eq2
  -- $f(f(10))=f(2)=1$
  rw [eq1, eq2]
