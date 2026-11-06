import Mathlib

lemma lemma1 (N : ℕ) : ∑ k ∈ Finset.Icc 1 N, (k : ℤ) = (N * (N + 1))/2 :=
by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [←Finset.sum_Ico_add_eq_sum_Icc]
      have : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
        ext l
        simp
        omega
      rw [this]
      rw [ih]
      push_cast
      conv =>
        lhs
        rhs
        rw [show (N + 1 : ℤ) = 2 * (N + 1) / 2 by omega]
      rw [←Int.add_ediv_of_dvd_left]
      congr
      ring_nf
      rcases em (Even N) with (h|h)
      . rcases h with ⟨n, h⟩
        rw [h]
        use n * (n * 2 + 1)
        push_cast
        ring_nf
      . have : Even (N + 1) := by exact Nat.even_add_one.mpr h
        rcases this with ⟨n, h⟩
        zify at h
        rw [h]
        use N * n
        ring_nf
      omega

lemma lemma2 (N : ℕ) : ∑ k ∈ Finset.Icc 1 N, k^2 = N * (N + 1) * (2 * N + 1) / 6 :=
by
  induction N with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ih]
    simp [Nat.mul_add, Nat.add_mul, pow_two]
    ring_nf
    omega

lemma lemma3 (N : ℕ) (hN : N > 0) : 3 ∣ N * (4 * N ^ 2 - 1) := by
  have : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by
    omega
  rcases this with (h|h|h)
  · have : (N * (4 * N ^ 2 - 1)) % 3 = 0 := by
      simp [Nat.mul_mod, h]
    omega
  · have : (N * (4 * N ^ 2 - 1)) % 3 = 0 := by
      simp [Nat.mul_mod, Nat.pow_mod, h, Nat.sub_mod_eq_zero_of_mod_eq]
    omega
  · have : (N * (4 * N ^ 2 - 1)) % 3 = 0 := by
      simp [Nat.mul_mod, Nat.pow_mod, h, Nat.sub_mod_eq_zero_of_mod_eq]
    omega

-- Let $L$ be an odd positive integer, and let $N = (L+1)/2$. Determine the remainder when the sum $1^{2}+3^{2}+5^{2}+\cdots+L^{2}$ is divided by 1000. Show that this remainder is equal to $( (4N^3 - N) \cdot 667 ) \pmod{1000}$.
theorem number_theory_640357
  {L : ℕ}
  (hL : Odd L)
  (hL1 : L > 0)
  (N : ℕ)
  (hN : N = (L + 1) / 2)
  : (∑ k ∈ Finset.Icc 1 N, (2 * k - 1 : ℤ)^2) % 1000 = ((4 * N^3 - N) * 667) % 1000 :=
by
  -- Step 1: Express the sum $S$ in terms of $N$.
  conv =>
    lhs
    lhs
    rhs
    intro k
    ring_nf
  rw[Finset.sum_add_distrib]
  rw[Finset.sum_sub_distrib]
  simp
  conv =>
    lhs
    lhs
    lhs
    rhs
    rhs
    intro k
    rw [mul_comm]
    change (4 • k)
  rw [Finset.sum_nsmul]
  rw [lemma1]
  conv =>
    lhs
    lhs
    rhs
    rhs
    intro k
    rw [mul_comm]
    change (4 • _)
  rw [Finset.sum_nsmul]
  have lemma2' := lemma2 N
  zify at lemma2'
  rw [lemma2']

  -- The general term is $(2k-1)^2 = 4k^2 - 4k + 1$, so
  -- $$S = \sum_{k=1}^{N} (4k^2 - 4k + 1) = 4 \sum_{k=1}^{N} k^2 - 4 \sum_{k=1}^{N} k + \sum_{k=1}^{N} 1.$$
  -- Using standard formulas:
  -- $\sum_{k=1}^{N} k = \frac{N(N+1)}{2}$,
  -- $\sum_{k=1}^{N} k^2 = \frac{N(N+1)(2N+1)}{6}$,
  -- $\sum_{k=1}^{N} 1 = N$.
  -- Substituting, we get:
  -- $$S = 4 \cdot \frac{N(N+1)(2N+1)}{6} - 4 \cdot \frac{N(N+1)}{2} + N = \frac{2N(N+1)(2N+1)}{3} - 2N(N+1) + N.$$
  have : (↑N - 4 • (↑N * (↑N + 1) / 2) + 4 • (↑N * (↑N + 1) * (2 * ↑N + 1) / 6) : ℤ)
       = (N * (4 * N^2 - 1)) / 3 :=
  by
    apply @Int.eq_of_mul_eq_mul_right 3
    . simp
    rw [Int.ediv_mul_cancel]
    qify
    simp
    rw [Int.cast_div, Int.cast_div]
    push_cast
    ring_nf
    -- Step 2: Show $S$ is always an integer.
    have : 6 ∣ N * (N + 1) * (2 * N + 1) := by
      clear *-
      induction N with
      | zero =>
        simp
      | succ k ih =>
        have : (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) =
          (k * (k + 1) * (2 * k + 1)) + 6 * (k + 1) ^ 2 := by
          ring_nf
        rw [this]
        omega
    zify at this
    assumption
    simp
    rcases em (Even N) with (h|h)
    . rcases h with ⟨n, h⟩
      rw [h]
      use n * (n * 2 + 1)
      push_cast
      ring_nf
    . have : Even (N + 1) := by exact Nat.even_add_one.mpr h
      rcases this with ⟨n, h⟩
      zify at h
      rw [h]
      use N * n
      ring_nf
    simp
    have Npos : N > 0 := by
      rw [hN]
      omega
    have lemma3' := lemma3 N Npos
    zify at lemma3'
    rw [Nat.cast_sub] at lemma3'
    push_cast at lemma3'
    assumption
    trans 4 * 1
    . simp
    . refine Nat.mul_le_mul ?_ ?_
      simp
      exact Nat.one_le_pow 2 N Npos
  rw [this]
  have : N * (4 * N ^ 2 - 1 : ℤ) = (4 * N^3 - N) := by
    linarith
  rw [this]
  have : (4 * ↑N ^ 3 - ↑N : ℤ) % 3 = 0 := by
    have : (↑N : ℤ) % 3 = 0 ∨ (↑N : ℤ) % 3 = 1 ∨ (↑N : ℤ) % 3 = 2 := by
      omega
    rcases this with (h | h | h)
    <;> simp [h, pow_succ, Int.mul_emod, Int.sub_emod]
  omega
