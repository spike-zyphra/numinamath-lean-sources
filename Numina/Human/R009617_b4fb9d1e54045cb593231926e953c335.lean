import Mathlib

/- Let  \begin{align*}
f(x) &= 2x + 5 \\
g(x) &= \sqrt{f(x)} - 2 \\
h(x) &= f(g(x))
\end{align*} What is $h(2)$? -/
theorem algebra_13055 {f g h : ℝ → ℝ}
    (hf : ∀ x, f x = 2 * x + 5)
    (hg : ∀ x, g x = Real.sqrt (f x) - 2)
    (hh : ∀ x, h x = f (g x)) :
    h 2 = 7 := by
  have h1 : f 2 = 2 * 2 + 5 := by rw [hf]
  have h2 : g 2 = Real.sqrt (f 2) - 2 := by rw [hg]
  have h3 : h 2 = f (g 2) := by rw [hh]
  rw [h1] at h2
  rw [h2] at h3
  have h4 : Real.sqrt (2 * 2 + 5) = 3 := by norm_num [Real.sqrt_eq_iff_sq_eq]
  rw [h4] at h3
  norm_num [hf, hg] at h3
  exact h3