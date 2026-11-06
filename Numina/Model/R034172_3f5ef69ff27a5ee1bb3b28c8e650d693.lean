import Mathlib

theorem algebra_598766 (a : ℕ → ℝ) (ha : ∀ i, ∃ c, 0 ≤ a i ∧ a i ≤ c)
    (hij : ∀ i j, i ≠ j → |a i - a j| ≥ 1 / (i + j)) :
    ∀ i, ∃ c, 0 ≤ a i ∧ a i ≤ c ∧ c ≥ 1 := by
  intro i
  have h1 := ha i
  rcases h1 with ⟨c, ha0, ha1⟩
  use max c 1
  constructor
  · -- Show that $0 \leq a i$.
    linarith
  constructor
  · -- Show that $a i \leq \max c 1$.
    cases max_cases c 1 with
    | inl h =>
      nlinarith
    | inr h =>
      nlinarith
  · -- Show that $\max c 1 \geq 1$.
    cases max_cases c 1 with
    | inl h =>
      nlinarith
    | inr h =>
      nlinarith