import Mathlib

/- Given two real numbers $1<p<q$ so that $\frac{1}{p} + \frac{1}{q} = 1$ and $pq = \frac{9}{2}$, what is $q$? -/
theorem algebra_17113 {p q : ℝ} (hp : 1 < p) (hq : p < q)
    (h₁ : 1 / p + 1 / q = 1) (h₂ : p * q = 9 / 2) : q = 3 := by
  have h₃ : q ≠ 0 := by linarith
  field_simp at h₁
  nlinarith