import Mathlib
/- The sum of the first $n$ terms of the arithmetic sequence $\left{ {{a}_ {n}} \right}$ is ${{S}_ {n}}$. It is known that ${{S}_ {10}}=0$ and ${{S}_ {15}}=25$. The minimum value of $n{{S}_ {n}}$ is __ _ ___ . -/
theorem algebra_623484 (d : ℝ) (a S : ℕ → ℝ) (ha : ∀ n : ℕ, a n = a 0 + n * d) (hS : ∀ n : ℕ, S n = ∑ i in Finset.range n, a i) (h1 : S 10 = 0) (h2 : S 15 = 25) : IsLeast {b : ℝ | ∃ n : ℕ, n ≥ 1 ∧ b = n * S n} (-49):= by
  have h : ∀ n : ℕ, S (n + 1) = (n + 1) * a 0 + n * (n + 1) * d / 2:= by
    intro n
    -- Prove by induction on n
    induction n with
    | zero =>
      -- Base case: n = 0
      simp [hS]
    | succ n ih =>
      -- Inductive step: assume true for n, prove for n+1
      rw [hS (n + 1 + 1), Finset.sum_range_succ, ←hS (n + 1), ih, ha (n + 1)]
      simp
      linarith

  -- Apply the formula to the given conditions
  rw [h 9] at h1
  rw [h 14] at h2
  simp at h1 h2

  -- Solve for d using S₁₀ = 0
  replace h1 : d = 2 / 3:= by linarith
  -- Solve for a₀ using S₁₅ = 25
  replace h2 : a 0 = -3:= by linarith

  -- Substitute the values back into the formula
  rw [h1, h2] at h

  -- Derive the simplified formula for Sₙ when n ≥ 1
  replace h : ∀ n : ℕ, n ≥ 1 → S n = 1 / 3 * n ^ 2 - 10 / 3 * n:= by
    intro n hn
    -- Use substitution m = n - 1 to apply our formula
    set m:= n - 1 with hm
    clear_value m
    replace hm : n = m + 1:= by omega
    subst n
    rw [h m]
    simp
    linarith

  -- Prove that -49 is the least element
  constructor
  .
    -- First part: show that -49 is in the set (achieved at n = 7)
    simp
    use 7
    simp
    rw [h 7 (by omega)]
    simp
    norm_num
  .
    -- Second part: show that -49 is a lower bound for all elements in the set
    simp [lowerBounds]
    intro a n hn ha
    subst a
    rw [h n hn]
    field_simp
    -- Show that n·Sₙ ≥ -49 for all n ≥ 1
    suffices n * ((↑n : ℤ) ^ 2 - 10 * n) ≥ -147 by rify at this ; linarith
    -- Convert to integer arithmetic for easier manipulation
    set m:= (↑n : ℤ) with hm
    clear_value m
    replace hm : m ≥ 0:= by linarith
    -- Case analysis: m ≥ 10 or m < 10
    by_cases hm1 : m ≥ 10
    .
      -- Case 1: m ≥ 10, then m(m²-10m) = m²(m-10) ≥ 0 > -147
      replace hm1 : m - 10 ≥ 0:= by omega
      replace hm1 : m ^ 2 * (m - 10) ≥ 0:= by positivity
      linarith
    .
      -- Case 2: m < 10, check all possible values m ∈ {0,1,2,...,9}
      replace hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9:= by omega
      rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
      -- Verify the inequality for each specific value
      all_goals
        subst m
        simp
