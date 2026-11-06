import Mathlib

theorem algebra_277879 (α : ℕ → ℕ → ℝ)
    (hα₀ : α 1 1 = 2)
    (hα₁ : ∀ n k, α (n + 1) k = 2 * (α n k)^3)
    (hα₂ : ∀ n k, α (n + 1) (k + 2^n - 1) = (1 / 2) * (α n k)^3) :
    ∀ m k, α m k ≠ α m (k + 1) := by
  have h1 := hα₁ 0 1
  have h1' := hα₁ 1 0
  have h1'' := hα₂ 1 0
  have h2 := hα₁ 0 0
  have h3 := hα₂ 0 1
  norm_num at h1 h1' h1'' h2 h3
  all_goals linarith