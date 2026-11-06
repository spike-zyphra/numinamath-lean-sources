import Mathlib

theorem algebra_13631 (a : ℕ → ℕ)
    (h₀ : a 1 = 10)
    (h₁ : ∀ m ≥ 1, a (m + 1) = a m + 2 * a 1) :
    a 2021 = 40410 := by
  have h2 : ∀ n, a (n + 1) = 10 + (n) * 20 := by
    intro n
    induction n with
    | zero =>
      simp [h₀]
    | succ n ih =>
      have h3 := h₁ (n + 1) (by omega)
      simp [show n + 1 + 1 = n + 2 by omega] at h3 ⊢
      rw [h3]
      rw [ih]
      simp [h₀]
      all_goals ring
  calc
    a 2021 = 10 + (2020) * 20 := h2 2020
    _ = 10 + 40400 := by omega
    _ = 40410 := by omega