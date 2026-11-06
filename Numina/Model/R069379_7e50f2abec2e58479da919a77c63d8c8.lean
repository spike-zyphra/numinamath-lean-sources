import Mathlib

theorem algebra_193702 (a : ℕ → ℤ) (ha : a 0 = 21) (h : ∀ n, a (n + 1) = a n - 4) :
    IsLeast {x | ∃ n, x = ∑ i in Finset.range (n + 1), a i ∧ |x - 55| = 1} 56 := by
  constructor
  · -- Let's prove 56 is in the set
    use 7
    constructor
    · -- Show that the sum equals 56
      norm_num [Finset.sum_range_succ, ha, h]
    · -- Show that |56 - 55| = 1
      norm_num
  · -- Now, let's show that 56 is the smallest
    intro x hx
    rcases hx with ⟨n, rfl, h1⟩
    have h2 : (∑ i in Finset.range (n + 1), a i) - 55 = 1 ∨ (∑ i in Finset.range (n + 1), a i) - 55 = -1 := by
      cases eq_or_eq_neg_of_abs_eq h1 with
      | inl h3 =>
        left
        linarith
      | inr h4 =>
        right
        linarith
    cases h2 with
    | inl h3 =>
      linarith
    | inr h4 =>
      have h4' : (∑ i in Finset.range (n + 1), a i) = 54 := by linarith
      have h1 : ∀ n, a n = 21 - 4 * n := by
        intro n
        induction n with
        | zero =>
          simp [ha]
        | succ n ih =>
          calc
            a (n + 1) = a n - 4 := h n
            _ = (21 - 4 * n) - 4 := by rw [ih]
            _ = 21 - 4 * (n + 1) := by ring
      have h5 : ∀ n, ∑ i in Finset.range (n + 1), a i = (n + 1) * (21 - 2 * n) := by
        intro n
        induction n with
        | zero =>
          simp [Finset.sum_range_succ, ha]
          <;> linarith
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          simp [h1]
          <;> ring_nf <;> linarith
      have h3 := h5 n
      rw [h3] at h4'
      have h6 : (n + 1 : ℤ) * (21 - 2 * n : ℤ) = 54 := by
        linarith
      have h7 : n ≤ 10 := by
        nlinarith [sq_nonneg (n : ℤ), sq_nonneg (21 - 2 * n : ℤ)]
      interval_cases n <;> omega