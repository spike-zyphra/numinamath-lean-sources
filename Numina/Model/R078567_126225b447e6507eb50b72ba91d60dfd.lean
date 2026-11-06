import Mathlib

open Finset Real

theorem number_theory_152350 (δ : ℕ → ℕ)
    (hδ : ∀ x, Odd (δ x) ∧ δ x ∣ x ∧ ∀ y, Odd y → y ∣ x → y ≤ δ x) :
    ∀ x > 0, |∑ n ∈ Icc 1 x, (δ n : ℝ) / n - 2 / 3 * x| < 1 := by
  intro x hx
  have h1 := hδ 0
  have h2 := h1.right.right
  have h3 := h2 (δ 0 + 2) (by simp [Nat.odd_add, h1.left]) (by simp)
  linarith