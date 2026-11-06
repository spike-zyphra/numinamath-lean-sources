import Mathlib

/- In the sequence $\left\{a_{n}\right\}$, $a_{1}=2, a_{2}=10$, for all positive integers $n$ we have $a_{n+2}=a_{n+1}-a_{n}$. Then $a_{2015}=$-/
theorem algebra_321316 (a : ℕ → ℤ) (ha1 : a 1 = 2) (ha2 : a 2 = 10) (hn : ∀ n > 0, a (n + 2) = a (n + 1) - a n) : a 2015 = - 10 := by
  -- Upon inspection, the sequence $\left\{a_{n}\right\}$ has a period of 6. 
  have h1 : ∀ n > 0, a (n + 6) = a n := by
    intro n hn'
    have h2 := hn n (by linarith)
    have h3 := hn (n + 1) (by linarith)
    have h4 := hn (n + 2) (by linarith)
    have h5 := hn (n + 3) (by linarith)
    have h6 := hn (n + 4) (by linarith)
    ring_nf at h2 h3 h4 h5 h6
    ring_nf ;rw [h6,h5,h4,h3,h2] ;ring_nf
  have h2 : ∀ n > 0, ∀ k, a (n + 6 * k) = a n := by
    intro n hn' k
    induction k with
    | zero => simp
    | succ k ih =>
      specialize h1  (n + 6 * k) (by linarith)
      ring_nf ;ring_nf at ih h1
      rw [h1,ih]
  -- Therefore, $$ a_{2015}=a_{335 \times 6+5}=a_{5}=-10 \text {. } $$
  specialize h2 5 (by simp) 335
  norm_num at h2
  rw [h2]
  simp [hn,ha1,ha2]
