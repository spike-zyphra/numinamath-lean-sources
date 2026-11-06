import Mathlib

/- Given that $$(m+n+p)(mn+mp+np)=25$$ and that $$m^2(n+p)+n^2(m+p)+p^2(m+n)=4$$ for real numbers $m$, $n$, and $p$, what is the value of $mnp$? -/
theorem algebra_19508 {m n p : ℝ} (h1 : (m + n + p) * (m * n + m * p + n * p) = 25)
    (h2 : m ^ 2 * (n + p) + n ^ 2 * (m + p) + p ^ 2 * (m + n) = 4) :
    m * n * p = 7 := by
  -- expand the first equation
  have h3: (m + n + p) * (m * n + m * p + n * p) =
  3*(m*n*p) + (m^2*n+m^2*p+m*n^2+n^2*p+m*p^2+n*p^2) := by ring
  -- expand the second equation
  have h4: m^2*(n+p)+n^2*(m+p)+p^2*(m+n) =
    (m^2*n+m^2*p+m*n^2+n^2*p+m*p^2+n*p^2) := by ring
  -- so we can substitute the second into the frist one
  rw [h4] at h2
  rw [h3] at h1
  rw [h2] at h1
  -- 3mnp+4=25, so 3mnp = 21
  have h5: 3*(m*n*p) = 21 := by
    have: (21:ℝ) = 25-4 := by norm_num
    rw [this, ← h1]; ring
  -- so mnp=7
  linarith [h5]