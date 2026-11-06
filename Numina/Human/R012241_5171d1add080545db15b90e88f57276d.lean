import Mathlib
/- Compute $1 \cdot 2+2 \cdot 3+\cdots+(n-1) n$. -/
theorem algebra_610897 (n : ℕ) : ∑ i in Finset.range (n - 1), (i + 1) * (i + 2) = (n - 1) * n * (n + 1) / 3:= by
  -- Handle base cases where n ≤ 1
  by_cases hn : n ≤ 1
  .
    -- Split into cases where n = 0 or n = 1
    replace hn : n = 1 ∨ n = 0:= by omega
    rcases hn with hn | hn
    all_goals
      subst n
      simp
  .
    -- Handle the main case where n > 1
    simp at hn
    replace hn : n - 1 > 0:= by omega
    -- Let m = n - 1 for easier manipulation
    set m:= n - 1 with hm
    clear_value m
    replace hm : n = m + 1:= by omega
    subst n
    rw [show m + 1 + 1 = m + 2 by ring]
    -- Prove by induction that 3 * sum = m(m+1)(m+2)
    have h1 : ∀ m : ℕ, 3 * ∑ i ∈ Finset.range m, (i + 1) * (i + 2) = m * (m + 1) * (m + 2):= by
      intro m
      induction m with
      -- Base case: m = 0
      | zero =>
        simp
      -- Inductive step: prove for m + 1 using the case for m
      | succ m ih =>
        simp [Finset.sum_range_succ]
        rw [show 3 * (∑ i ∈ Finset.range m, (i + 1) * (i + 2) + (m + 1) * (m + 2)) = 3 * (∑ i ∈ Finset.range m, (i + 1) * (i + 2)) + 3 * (m + 1) * (m + 2) by ring]
        rw [ih]
        rify
        linarith
    -- Apply the proven equality to our specific case
    specialize h1 m
    refine Nat.eq_div_of_mul_eq_right (by omega) h1
