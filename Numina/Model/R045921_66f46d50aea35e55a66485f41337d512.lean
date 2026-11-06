import Mathlib

theorem algebra_255056 (τ : ℝ) (hτ : τ > 0) :
    ∃ (s : ℕ → ℝ), ∀ (i j : ℕ), i > 0 ∧ j > 0 → s i / s j = i / j := by 
  use fun (n : ℕ) => (n : ℝ)
  intro i j h
  rcases h with ⟨hi, hj⟩
  simp at *
  <;> field_simp
  <;> ring