import Mathlib

/- Suppose that $a$ and $b$ are positive real numbers, and let \[f(x) =
\begin{cases}
\frac{a}{b}x & \text{ if }x\le-4, \\
abx^2 & \text{ if }x>-4.
\end{cases}
\]If $f(-4)=-\frac{60}{13}$ and $f(4)=3120$, what is $a+b$? -/
theorem algebra_20336 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f : ℝ → ℝ) (hf : ∀ x, x ≤ -4 → f x = a / b * x)
    (hf' : ∀ x, x > -4 → f x = a * b * x ^ 2) (h₁ : f (-4) = -60 / 13)
    (h₂ : f 4 = 3120) : a + b = 28 := by
  have h₁' := hf (-4)
  have h₂' := hf' 4
  simp at h₁' h₂'
  norm_num at h₁' h₂'
  have hb' : b ≠ 0 := ne_of_gt hb
  have ha' : a ≠ 0 := ne_of_gt ha
  field_simp at h₁' h₂'
  nlinarith