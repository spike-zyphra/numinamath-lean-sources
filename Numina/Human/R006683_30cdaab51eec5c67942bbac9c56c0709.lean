import Mathlib

/-Theorem: Let $k$ be a natural number. Let $N$ be a positive natural number. Suppose that the product of $N$, $k$, $11$ (the number of grandchildren), and $91$ (the age of a patriarch) is equal to the sum $1000N + 10N + N$. Show that $N=1$.-/
theorem number_theory_640101 (k N : ℕ) (hN : N > 0) (h : N * k * 11 * 91 = 1000 * N + 10 * N + N) : N = 1 := by
  have h₁ : N * (11 * 91 * k - 1011) = 0 := by
    rw [Nat.mul_sub]
    ring_nf at h ⊢
    simp [h]

  simp only [Nat.reduceMul, mul_eq_zero] at h₁
  obtain (h₁ | h₁) := h₁
  · -- N = 0, which contradicts hN
    linarith
  · -- 1001 * k - 1011 = 0, which implies k = 1011/1001. 1011/1001 is not a natural number
    have h₂ : 1001 * k ≥ 1011 := by
      simp only [Nat.reduceMul, ge_iff_le]
      by_cases hk: k = 0
      · rw [hk] at h
        norm_num at h
        linarith
      by_cases hk': k = 1
      · rw [hk'] at h
        norm_num at h
        linarith
      omega
    -- so, it is contradictory to assume k is a natural number too.
    -- Therefore, from the principle of explosion, we can conclude that N equals anything we want, so we can conclude that N = 1.
    omega
