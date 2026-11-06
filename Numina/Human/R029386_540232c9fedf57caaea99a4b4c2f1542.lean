import Mathlib

theorem algebra_239857 (a : ℕ → ℤ) (h₁ : a 1 = 1) (h₂ : a 2 = 3) (h₃ : ∀ n ≥ 2, a (n + 1) = 3 * a n - 2 * a (n - 1)) :
    a 1000 = 2 ^ 1000 - 1 := by
  suffices H : ∀ n ≥ 1, (a n = 2 ^ n - 1) ∧ (a (n + 1) = 2 ^ (n + 1) - 1) from (H 1000 (by simp)).1
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [h₁, h₂]
  | succ n hn ih =>
    use ih.2
    simp [h₃ (n + 1) (Nat.le_add_of_sub_le hn), ih]
    ring