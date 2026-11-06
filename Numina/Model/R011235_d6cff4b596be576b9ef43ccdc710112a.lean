import Mathlib

theorem algebra_8984 (n : ℕ) (hn : n > 0) :
  ∑ i ∈ Finset.range n, (i + 1) * (i + 4) = (n : ℝ) * (n + 1) * (n + 5) / 3 := by
  have h1 : ∀ (n : ℕ), n > 0 → (∑ i in Finset.range n, (i + 1) * (i + 4) : ℝ) = (n : ℝ) * (n + 1) * (n + 5) / 3 := by
    intro n hn
    induction n with
    | zero =>
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        norm_num at ih ⊢
        all_goals 
          linarith
      | succ n =>
        rw [Finset.sum_range_succ, ih (by linarith) ]
        field_simp
        ring
  specialize h1 n hn
  simpa using h1