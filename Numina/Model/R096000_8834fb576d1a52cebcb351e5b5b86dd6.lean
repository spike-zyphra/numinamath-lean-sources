import Mathlib

theorem algebra_94950 (a : ℕ → ℤ)
    (h₀ : a 1 = 2)
    (h₁ : ∀ n ≥ 1, a (n + 1) = a n + 2 * n) :
    a 100 = 9902 := by
  have h2 : ∀ (n : ℕ), a (n + 1) = (n + 1 : ℤ) ^ 2 - (n + 1 : ℤ) + 2 := by
    intro n
    induction n with
    | zero =>
      -- Base case: a 1 = 2
      simp [h₀]
      <;> try tauto
      <;> try ring_nf
      <;> try linarith
      <;> try omega
    | succ n ih =>
      -- Assume true for n, prove for n+1
      have eq1 : a ((n + 1) + 1) = a (n + 1) + 2 * ((n + 1 : ℕ): ℤ) := h₁ (n + 1) (by linarith)
      rw [eq1]
      rw [ih]
      -- Now do algebraic manipulation
      simp [pow_two]
      <;> try ring_nf
      <;> try nlinarith
      <;> try omega
      all_goals try linarith
      all_goals try tauto
      all_goals try nlinarith
  specialize h2 99
  norm_num at h2 ⊢
  <;> try linarith
  <;> try tauto
  all_goals try nlinarith