import Mathlib
theorem algebra_610897 (n : ℕ) : ∑ i in Finset.range (n - 1), (i + 1) * (i + 2) = (n - 1) * n * (n + 1) / 3:= by
  by_cases hn : n ≤ 1
  · -- Case where n ≤ 1, so n = 0 or 1
    replace hn : n = 0 ∨ n = 1:= by omega
    rcases hn with hn | hn
    · -- n = 0
      subst n
      all_goals simp
    · -- n = 1
      subst n
      all_goals simp
  · -- Case where n > 1
    have h1 : n ≥ 2 := by omega
    have h2 : ∀ (k : ℕ), k ≥ 2 → ∑ i in Finset.range (k - 1), (i + 1) * (i + 2) = (k - 1) * k * (k + 1) / 3 := by
      intro k hk
      induction k with
      | zero =>
        linarith
      | succ k ih =>
        cases k with
        | zero =>
          all_goals simp at ih ⊢
        | succ k =>
          cases k with
          | zero =>
            all_goals simp at ih ⊢
          | succ k =>
            simp [Finset.sum_range_succ, mul_add, add_mul] at ih ⊢
            ring_nf at ih ⊢
            all_goals omega
    have h3 := h2 n (by omega)
    simpa using h3