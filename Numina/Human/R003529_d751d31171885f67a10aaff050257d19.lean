import Mathlib
/- 14. [40] A number $n$ is called bummed out if there is exactly one ordered pair of positive integers $(x, y)$ such that
$$
\left\lfloor x^{2} / y\right\rfloor+\left\lfloor y^{2} / x\right\rfloor=n .
$$

Find all bummed out numbers. -/
theorem number_theory_192070 : {n : ℕ | ∃! x : ℕ × ℕ, 0 < x.1 ∧ 0 < x.2 ∧ ⌊(x.1 : ℝ) ^ 2 / x.2⌋ + ⌊(x.2 : ℝ) ^ 2 / x.1⌋ = n} = {2, 6, 8, 10}:= by
  ext n
  constructor
  .
    -- Forward direction: if n is bummed out, then n ∈ {2, 6, 8, 10}
    intro h
    simp at h
    rcases h with ⟨⟨x, y⟩, h1, h2⟩
    simp at h1
    rcases h1 with ⟨hx, hy, h⟩

    -- Show that x = y for the unique solution
    have h1 : x = y:= by
      replace h2:= h2 ⟨y, x⟩
      simp at h2
      replace h2:= h2 hy hx (by linarith)
      exact h2.2
    subst y

    -- Simplify the expression since x = y
    rw [show (x : ℝ) ^ 2 / x = x by field_simp ; ring] at h
    simp at h

    -- Show that n ≠ 0
    have hne0 : n ≠ 0:= by
      by_contra H
      subst n
      simp at h
      linarith

    -- Show that n must be even
    replace h : Even n:= by
      use x
      zify
      linarith
    rcases h with ⟨n, rfl⟩
    rw [show n + n = 2 * n by ring] at h2 ⊢
    simp at h2

    -- Show that n ≠ 2 (i.e., k ≠ 1)
    have h1 : n ≠ 2:= by
      by_contra H
      subst n
      simp at h2
      replace h2:= h2 1 2 (by simp) (by simp) (by norm_num)
      rcases h2 with ⟨h2, h3⟩
      linarith

    -- Show that n ≤ 10 (i.e., k ≤ 5)
    have h3 : n ≤ 5:= by
      by_contra H
      replace H : n ≥ 6:= by omega
      replace h2:= h2 (n - 1) (n + 1) (by omega) (by omega) ?_
      rcases h2 with ⟨h2, h3⟩
      omega
      have g : n ≥ 1:= by omega
      field_simp
      replace g : (n : ℝ) - 1 > 0:= by
        rify at H
        linarith

      -- Calculate floor((n-1)²/(n+1))
      rw [show ((↑n : ℝ) - 1) ^ 2 / (↑n + 1) = n - 3 + 4 / (n + 1) by field_simp ; ring]
      rw [show ((↑n : ℝ) + 1) ^ 2 / (↑n - 1) = n + 3 + 4 / (n - 1) by field_simp ; ring]

      -- Show floor((n-1)²/(n+1)) = n - 3
      have g1 : ⌊(↑n : ℝ) - 3 + 4 / (↑n + 1)⌋ = n - 3:= by
        refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
        simp
        positivity
        simp
        have g1 : (n : ℝ) + 1 > 0:= by positivity
        suffices 4 < (n : ℝ) + 1 by exact Bound.div_lt_one_of_pos_of_lt g1 this
        rify at H
        linarith

      -- Show floor((n+1)²/(n-1)) = n + 3
      have g2 : ⌊(↑n : ℝ) + 3 + 4 / (↑n - 1)⌋ = n + 3:= by
        refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
        simp
        positivity
        simp
        have g2 : (n : ℝ) - 1 > 0:= by positivity
        suffices 4 < (n : ℝ) - 1 by exact Bound.div_lt_one_of_pos_of_lt g2 this
        rify at H
        linarith
      linarith
    simp
    omega
  .
    -- Backward direction: if n ∈ {2, 6, 8, 10}, then n is bummed out
    intro h
    simp at h ⊢

    -- Express n as 2*k where k ∈ {1, 3, 4, 5}
    replace h : ∃ k : ℕ, n = 2 * k ∧ (k = 1 ∨ k = 3 ∨ k = 4 ∨ k = 5):= by
      rcases h with rfl | rfl | rfl | rfl
      .
        use 1
        simp
      .
        use 3
        simp
      .
        use 4
        simp
      .
        use 5
        simp
    rcases h with ⟨k, rfl, h⟩

    -- Show that (k, k) is a solution
    use ⟨k, k⟩
    simp
    constructor
    .
      -- Verify that (k, k) satisfies the equation
      refine ⟨by omega, ?_⟩
      replace h : k > 0:= by omega
      rify at h
      rw [show (↑k : ℝ) ^ 2 / ↑k = k by field_simp ; ring]
      simp
      ring
    .
      -- Show that (k, k) is the unique solution
      intro a b ha hb hab

      -- Use floor properties to get bounds
      have ga:= Int.lt_floor_add_one ((↑a : ℝ) ^ 2 / ↑b)
      have gb:= Int.lt_floor_add_one ((↑b : ℝ) ^ 2 / ↑a)

      -- Show that the expression is non-negative
      have g : (a : ℝ) ^ 2 / b + b ^ 2 / a - (a + b) ≥ 0:= by
        rw [show (a : ℝ) ^ 2 / b + b ^ 2 / a - (a + b) = (a + b) * (a - b) ^ 2 / (a * b) by field_simp ; ring]
        positivity

      -- Get upper bound on a + b
      have g1 : a + b < 2 * k + 2:= by
        rify at hab ⊢
        linarith
      have ha1 : a ∈ Finset.range (2 * k + 2):= by simp ; omega
      have hb1 : b ∈ Finset.range (2 * k + 2):= by simp ; omega

      -- Use contradiction to show uniqueness
      by_contra H
      rcases h with rfl | rfl | rfl | rfl
      all_goals
        fin_cases ha1
        all_goals
          fin_cases hb1
          all_goals
            norm_num at hab H
