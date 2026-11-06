import Mathlib

/- Let $N$ be a positive integer. Let $[x]$ denote the greatest integer not exceeding $x$. Let $M = [ \sqrt{N} ]$. Find the value of the sum $S_N = \sum_{k=1}^{N} [ \sqrt{k} ]$. Show the answer is $M(N - M^2 + 1) + \frac{(M-1)M(4M+1)}{6}$. -/
theorem number_theory_640394 (n m : ℕ) (hn : n > 0) (hm : m = ⌊√n⌋) : ∑ i in Finset.range n, ⌊√(i + 1)⌋ = m * (n - m ^ 2 + 1) + (m - 1) * m * (4 * m + 1) / 6:= by
  -- Prove that n ≥ m^2 using properties of floor function
  have h1 : n ≥ m ^ 2:= by
    rify at hm
    have h1 : m ≤ √n:= by
      rw [hm]
      exact Int.floor_le √↑n
    rw [show (↑m : ℝ) = |(↑m : ℝ)| by exact Eq.symm (abs_of_nonneg (by rw [hm] ; positivity))] at h1
    rw [show √n = |√n| by exact Eq.symm (abs_of_nonneg (by positivity))] at h1
    replace h1 : m ^ 2 ≤ √n ^ 2:= by exact sq_le_sq.mpr h1
    field_simp at h1
    rify
    linarith

  -- Prove that n < (m+1)^2 using properties of floor function
  have h2 : n < (m + 1) ^ 2:= by
    rify at hm
    have h2 : m + 1 > √n:= by
      rw [hm]
      exact Int.lt_floor_add_one √↑n
    rw [show (↑m : ℝ) + 1 = |(↑m : ℝ) + 1| by exact Eq.symm (abs_of_nonneg (by rw [hm] ; positivity))] at h2
    rw [show √n = |√n| by exact Eq.symm (abs_of_nonneg (by positivity))] at h2
    replace h2 : (m + 1) ^ 2 > √n ^ 2:= by exact sq_lt_sq.mpr h2
    field_simp at h2
    rify
    linarith

  -- Helper lemma: For any m and k where k+1 ≤ 2m,
  -- floor(sqrt(m^2 + k + 1)) = m
  have g : ∀ m k : ℕ, k + 1 ≤ 2 * m → ⌊√(↑m ^ 2 + ↑k + 1)⌋ = m:= by
    intro m k hmk
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    .
      simp
      suffices √(↑m ^ 2 + ↑k + 1) ≥ √(m ^ 2) by field_simp at this ; exact this
      suffices (↑m : ℝ) ^ 2 + ↑k + 1 ≥ m ^ 2 by exact Real.sqrt_le_sqrt this
      suffices m ^ 2 + k + 1 ≥ m ^ 2 by rify at this ; exact this
      omega
    .
      simp
      rw [show (↑m : ℝ) + 1 = |(↑m : ℝ) + 1| by exact Eq.symm (abs_of_nonneg (by positivity))]
      rw [show √(↑m ^ 2 + ↑k + 1) = |√(↑m ^ 2 + ↑k + 1)| by exact Eq.symm (abs_of_nonneg (by positivity))]
      suffices √(↑m ^ 2 + ↑k + 1) ^ 2 < (↑m + 1) ^ 2 by exact sq_lt_sq.mp this
      field_simp
      suffices m ^ 2 + k + 1 < (m + 1) ^ 2 by rify at this ; exact this
      linarith only [hmk]

  -- Define r as the difference between n and m^2
  set r:= n - m ^ 2 with hr
  clear_value r
  replace hn : n = m ^ 2 + r:= by omega
  replace h2 : r ≤ 2 * m:= by linarith
  clear h1 hr
  subst n
  clear hm

  -- Induction on r to prove the main theorem
  induction r with
  | zero =>
    simp
    clear h2
    induction m with
    | zero =>
      simp
    | succ m ih =>
      rw [show (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 by ring]
      rw [Finset.sum_range_succ]
      simp
      rw [show (↑m : ℝ) ^ 2 + 2 * ↑m + 1 = (m + 1) ^ 2 by ring_nf]
      field_simp
      have h1 : ∀ k : ℕ, k ≤ 2 * m → ∑ x ∈ Finset.range (m ^ 2 + k), ⌊√(↑x + 1)⌋ = ↑m + (↑m - 1) * ↑m * (4 * ↑m + 1) / 6 + k * m:= by
        intro k hk
        induction k with
        | zero =>
          simp
          exact ih
        | succ k ihk =>
          rw [show m ^ 2 + (k + 1) = m ^ 2 + k + 1 by ring]
          rw [Finset.sum_range_succ, ihk]
          simp
          rw [g m k hk]
          ring_nf
          omega
      rw [h1 (2 * m) (by omega)]
      simp
      rw [show (↑m : ℤ) * (↑m + 1) * (4 * (↑m + 1) + 1) = 6 * (2 * m ^ 2 + m) + (↑m - 1) * ↑m * (4 * ↑m + 1) by ring]
      rw [show (6 * (2 * (↑m : ℤ) ^ 2 + ↑m) + (↑m - 1) * ↑m * (4 * ↑m + 1)) / 6 = (2 * ↑m ^ 2 + ↑m) + ((↑m - 1) * ↑m * (4 * ↑m + 1)) / 6 by omega]
      ring_nf
  | succ i ih =>
    rw [show m ^ 2 + (i + 1) = m ^ 2 + i + 1 by ring]
    rw [Finset.sum_range_succ]
    simp
    rw [g m i h2, ih]
    simp
    ring_nf
    omega
