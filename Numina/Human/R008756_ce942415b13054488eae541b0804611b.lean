import Mathlib

/- Given $f(1,1)=1$, $f(m,n) \\in \\mathbb{N}^{+}$, for any $m,n \\in \\mathbb{N}^{+}$, we have: (1) $f(m,n+1)=f(m,n)+2$; (2) $f(m+1,1)=2f(m,1)$. Find the value of $f(11,11)$. -/
theorem algebra_430835 {f : ℕ → ℕ → ℕ} (h1 : f 1 1 = 1)
    (h2 : ∀ m n, 0 < m → 0 < n → f m n > 0)
    (h3 : ∀ m n, 0 < m → 0 < n → f m (n + 1) = f m n + 2)
    (h4 : ∀ m, 0 < m → f (m + 1) 1 = 2 * f m 1) :
    f 11 11 = 1044 := by
  have H m n (hm : 0 < m) (hn : 0 < n) : f m n = 2^(m-1) + 2*(n-1) := by
    induction n, hn using Nat.le_induction with
    | base =>
      simp
      induction m, hm using Nat.le_induction with
      | base =>
        simpa
      | succ m hm ih =>
        rw [h4 m hm, ih]
        rw [mul_comm, ← pow_succ]
        simp [hm]
    | succ n hn ih =>
      rw [h3 m n hm hn, ih]
      omega
  norm_num [H]
