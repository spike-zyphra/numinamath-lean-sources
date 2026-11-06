import Mathlib

theorem algebra_11137 (θ : ℝ) (hθ : θ ∈ Set.Icc 0 90) (supp comp : ℝ → ℝ)
    (hsupp : ∀ x, supp x = 180 - x) (hcomp : ∀ x, comp x = 90 - x)
    (h : supp θ = 6 * comp θ) :
    θ = 72 := by
  rcases hθ with ⟨h1, h2⟩
  have eq1 : supp θ = 180 - θ := hsupp θ
  have eq2 : comp θ = 90 - θ := hcomp θ
  rw [eq1] at h
  rw [eq2] at h
  linarith