import Mathlib

theorem algebra_9752
    (a : ℕ → ℝ)
    (h₀ : a 0 = 1)
    (h₁ : a 1 = 2)
    (h₂ : ∀ n, a (n + 2) - 3 * a (n + 1) + 2 * a n = 1)
    (T : ℕ → ℝ)
    (hT : ∀ n, T n = ∑ i in Finset.range n, 8 / a i) :
    ⌊T 2023⌋ = 14 := by

  -- Prove by induction the general formula of $a_n$.
  have h3 : ∀ n : ℕ, a n = (2 : ℝ) ^ (n + 1) - (n : ℝ) - 1 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      simp [h₀]
      <;> linarith
    | succ n =>
      cases n with
      | zero =>
        simp [h₁]
        <;> linarith
      | succ n =>
        have h₃ := h₂ n
        simp [ih (n + 1) (by linarith), ih (n) (by linarith)] at h₃ ⊢
        ring_nf at h₃ ⊢
        <;> nlinarith

  -- Derive the expression of $T_n$ from its definition.
  have h4 : T 2023 = ∑ i in Finset.range 2023, 8 / a i := by
    specialize hT 2023
    simpa using hT

  rw [h4]

  norm_num [Finset.sum_range_succ, h3]
  <;> try { native_decide }