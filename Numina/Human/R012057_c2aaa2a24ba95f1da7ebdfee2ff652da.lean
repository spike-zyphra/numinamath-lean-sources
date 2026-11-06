import Mathlib
/- 8・13 Let the sequence $\left\{x_{n}\right\}$ satisfy: $x_{1}=\frac{1}{2}$, and
$$x_{k+1}=x_{k}+x_{k}^{2}, k=1,2, \cdots$$

Find the integer part of $\frac{1}{x_{1}+1}+\frac{1}{x_{2}+1}+\cdots+\frac{1}{x_{100}+1}$. -/
theorem number_theory_598621 (x : ℕ → ℝ) (h1 : x 0 = 1 / 2) (hn : ∀ k : ℕ, x (k + 1) = x k + x k ^ 2) : ⌊∑ i in Finset.range 100, (1 / (x i + 1))⌋ = 1:= by
  -- First prove that all terms in the sequence are positive
  have hpos : ∀ k : ℕ, x k > 0:= by
    intro k
    induction k with
    | zero =>
      linarith
    | succ k ih =>
      rw [hn k]
      positivity

  -- Prove a key telescoping sum identity:
  -- Sum of 1/(x_i+1) from i=0 to k equals 1/x_0 - 1/x_(k+1)
  have h2 : ∀ k : ℕ, ∑ i in Finset.range (k + 1), (1 / (x i + 1)) = 1 / x 0 - 1 / x (k + 1):= by
    intro k
    induction k with
    | zero =>
      simp
      rw [hn 0, h1]
      norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      rw [hn (k + 1)]
      have g2:= hpos (k + 1)
      field_simp
      ring_nf

  -- Apply the telescoping sum identity with k=99 to get our target sum
  specialize h2 99
  rw [show 99 + 1 = 100 by norm_num] at h2
  set t:= ∑ i ∈ Finset.range 100, 1 / (x i + 1)
  clear_value t

  -- Prove that the sum is at least 1
  have ht1 : t ≥ 1:= by
    subst t
    rw [h1]
    field_simp
    -- Prove that x_k ≥ 1 for all k ≥ 2
    have h2 : ∀ k : ℕ, x (k + 2) ≥ 1:= by
      intro k
      induction k with
      | zero =>
        rw [hn 1, hn 0, h1]
        norm_num
      | succ k ih =>
        rw [show k + 1 + 2 = k + 2 + 1 by ring]
        rw [hn (k + 2)]
        have g : x (k + 2) ^ 2 ≥ 0:= by positivity
        linarith
    specialize h2 98
    rw [show 98 + 2 = 100 by norm_num] at h2
    replace h2 : 1 / x 100 ≤ 1:= by exact (div_le_one₀ (hpos 100)).mpr h2
    linarith

  -- Prove that the sum is less than 2
  have ht2 : t < 2:= by
    subst t
    rw [h1]
    field_simp
    exact hpos 100

  -- Conclude that the floor of the sum is 1
  refine Int.floor_eq_iff.mpr ⟨(by simp; linarith), (by simp; linarith)⟩
