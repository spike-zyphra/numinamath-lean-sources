import Mathlib

theorem algebra_215390 {a : ℕ → ℝ} (ha1 : a 1 = 7) (han : ∀ n ≥ 1, a (n + 1) / a n = a n + 2) :
    IsLeast {n | 0 < n ∧ a n > 4 ^ 2018} 12 := by
  have h1 : ∀ n ≥ 1, a (n + 1) = a n * (a n + 2) := by
    intro n hn
    have h1 := han n hn
    have hne : a n ≠ 0 := by
      by_contra h
      rw [h] at h1
      norm_num at h1
    field_simp [hne] at h1 ⊢
    linarith

  have eqn (n : ℕ) : a (n + 1) = (8 : ℝ) ^ (2 ^ n) - 1 := by
    induction n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n ih =>
      have eq1 : a (n + 2) = a (n + 1) * (a (n + 1) + 2) := by
        specialize h1 (n + 1) (by linarith)
        simpa using h1
      rw [eq1]
      rw [ih]
      ring_nf
  constructor
  · -- Show that 12 is in the set
    constructor
    · norm_num
    · -- Show that a 12 > 4 ^ 2018
      have eq12 := eqn 11
      norm_num at eq12 ⊢
      linarith
  · -- Show that 12 is the smallest element in the set
    intro n hn
    rcases hn with ⟨hn_pos, h⟩
    by_contra h'
    push_neg at h'
    have eqn (k : ℕ) : a (k + 1) = (8 : ℝ) ^ (2 ^ k) - 1 := by
      apply eqn
    have r1 : n < 12 := by linarith
    have eqn' : a n = (8 : ℝ) ^ (2 ^ (n - 1 : ℕ)) - 1 := by
      cases n with
      | zero =>
        linarith
      | succ n =>
        specialize eqn n
        simpa using eqn
    interval_cases n <;> norm_num [eqn] at h <;> norm_num at h <;> linarith