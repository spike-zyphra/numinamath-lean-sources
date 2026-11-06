import Mathlib

/- Given the sequence ${{a}_{n}}$ satisfies the recurrence relation ${{a}_{n+1}}=2{{a}_{n}}+{{2}^{n}}-1(n\in {{\mathbf{N}}_{+}})$, and $\frac{{{a}_{n}}+\lambda }{{{2}^{n}}}$ is an arithmetic sequence, then the value of $\lambda$ is ___          ___. -/
theorem algebra_12251 {a : ℕ → ℤ} (ha : ∀ n, a (n + 1) = 2 * a n + 2 ^ n - 1)
    (h : ∃ d, ∀ n, (a n + d) / 2 ^ n = (a 0 + d) / 2 ^ 0 + d * (n - 1)) :
    d = -1 := by 
  rcases h with ⟨d, hd⟩ 
  have h0 := hd 0
  norm_num at h0
  have h1 := hd 1
  have ha0 : a 1 = 2 * a 0 := by 
    specialize ha 0
    norm_num at ha
    omega
  norm_num [ha0] at h1
  have h2 := hd 2
  have ha1 : a 2 = 2 * a 1 + 2 ^ 1 - 1 := by 
    specialize ha 1
    norm_num at ha
    omega
  norm_num [ha0, ha1] at h2
  have h3 := hd 3
  have ha2 : a 3 = 2 * a 2 + 2 ^ 2 - 1 := by 
    specialize ha 2
    norm_num at ha
    omega
  norm_num [ha0, ha1, ha2] at h3
  have h4 := hd 4
  have ha3 : a 4 = 2 * a 3 + 2 ^ 3 - 1 := by 
    specialize ha 3
    norm_num at ha
    omega
  norm_num [ha0, ha1, ha2, ha3] at h4
  omega