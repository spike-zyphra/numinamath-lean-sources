import Mathlib

/- Let $k$ be a positive integer. Let $m$ and $n$ be positive integers such that the fraction $\frac{n}{m}$ satisfies the inequality $\frac{k}{k+1} < \frac{n}{m} < \frac{k+1}{k+2}$. Determine the fraction $\frac{n}{m}$ for which $m$ is the smallest possible positive integer. Show that this fraction is equal to $\frac{2k+1}{2k+3}$. -/
theorem number_theory (k : ℕ) (hk : 1 ≤ k) :
    IsLeast
      {m : ℕ
      | ∃ n : ℕ,
          0 < m
          ∧ 0 < n
          ∧ k / (k + 1 : ℚ) < n / m
          ∧ (n / m : ℚ) < (k + 1) / (k + 2)}
      (2 * k + 3) :=
by
  constructor
  . simp
    use (2*k+1)
    constructor
    . simp
    constructor
    . refine (div_lt_div_iff₀ ?_ ?_).mpr ?_
      all_goals
        norm_cast
        try omega
      ring_nf
      omega
    . refine (div_lt_div_iff₀ ?_ ?_).mpr ?_
      all_goals
        norm_cast
        try omega
      ring_nf
      omega
  -- Suppose m is any positive integer with n such that
  -- 0 < m, 0 < n, k/(k+1) < n/m < (k+1)/(k+2)
  rintro m ⟨n, mpos, npos, H1, H2⟩

  -- From k/(k+1) < n/m, we get n*(k+1) > m*k
  -- $n (k+1) > m k$
  have H1 : n * (k + 1) > m * k := by
    qify
    rw [mul_comm]
    refine (div_lt_div_iff₀ ?_ ?_).mp ?_
    all_goals
      norm_cast
      try omega
    push_cast at H1 ⊢
    exact H1

  -- From n/m < (k+1)/(k+2), we get n*(k+2) < m*(k+1)
  -- $n (k+2) < m (k+1)$
  have H2 : n * (k+2) < m * (k+1) := by
    qify
    rw [mul_comm (m : ℚ)]
    refine (div_lt_div_iff₀ ?_ ?_).mp ?_
    all_goals
      norm_cast
      try omega
    push_cast at H2 ⊢
    exact H2

  -- From n*(k+1) > m*k, we get n ≥ (m*k+1)/(k+1)
  -- $n \geq \frac{m k + 1}{k+1}$
  have : (n : ℚ) ≥ (m*k+1)/(k+1) := by
    have : n * (k+1) ≥ m * k + 1 := by omega
    qify at this
    apply div_le_of_le_mul₀
    all_goals
      norm_cast
      try omega

  -- From n*(k+2) < m*(k+1), we get n ≤ (m*(k+1) - 1)/(k+2)
  -- $n \leq \frac{m(k+1) - 1}{k+2}$
  have : (n : ℚ) ≤ (m*(k+1) - 1) / (k+2) := by
    have : n * (k + 2 : ℤ) ≤ m * (k + 1) - 1 := by
      zify at H2
      omega
    qify at this
    apply (le_div_iff₀' ?_).mpr
    linarith
    linarith

  -- Therefore, (m*k+1)/(k+1) ≤ (m*(k+1) - 1)/(k+2)
  -- $\frac{m k + 1}{k+1} \leq \frac{m(k+1) - 1}{k+2}$
  have : (m*k+1)/(k+1 : ℚ) ≤ (m*(k+1) - 1) / (k+2) := by
    calc
    _ ≤ (n : ℚ) := by assumption
    _ ≤ _ := by assumption

  -- Multiply both sides by (k+1)(k+2) to clear denominators:
  -- $(m k + 1)(k+2) \leq (m(k+1) - 1)(k+1)$
  have : (m*k + 1) * (k+2 : ℤ) ≤ (m * (k+1) - 1) * (k+1) := by
    qify
    apply (div_le_div_iff₀ ?_ ?_).mp
    . assumption
    all_goals
    norm_cast
    omega

  -- Now, simplify and deduce $m \geq 2k+3$
  zify
  ring_nf at this
  omega
