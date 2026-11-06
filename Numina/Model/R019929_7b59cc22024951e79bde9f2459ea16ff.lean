import Mathlib

open Real
open scoped BigOperators

theorem number_theory_113966 (δ : ℕ → ℕ)
  (hδ : ∀ x, Odd (δ x) ∧ δ x ∣ x ∧ ∀ y, Odd y → y ∣ x → y ≤ δ x) :
  ∀ x, 0 < x → |∑ n in Finset.Icc 1 x, (δ n : ℝ)/n - 2/3 * x| < 1 := by
  have h1 := hδ 0
  have h3 : Odd (δ 0) := h1.1
  -- Show that there exists a larger odd
  have h5 : δ 0 + 2 ∣ 0 := by
    simp
  have h6 : Odd (δ 0 + 2) := by
    obtain ⟨k, hk⟩ := h3
    use k + 1
    omega
  -- Apply the property of δ 0
  have h8 : δ 0 + 2 ≤ δ 0 := by
    apply h1.2.2 (δ 0 + 2) h6 h5
  -- Contradiction
  omega