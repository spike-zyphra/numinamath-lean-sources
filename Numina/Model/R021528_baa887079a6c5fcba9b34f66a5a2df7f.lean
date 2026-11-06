import Mathlib

theorem algebra_185721 {f g : ℝ → ℝ} (hf : f = fun x => x ^ 2)
    (hg : ∀ x, g (-x) = f x) (hS : g 0 = 6) (hperp : ∃ A B A1 B1 : ℝ,
    A ≠ B ∧ A1 ≠ B1 ∧ f A * g A = 1 ∧ f B * g B = 1 ∧
    dist A1 B1 = dist A B ∧ dist B1 A1 = dist B A) :
    g (2 * Real.sqrt 3) = 0 ∧ g (-2 * Real.sqrt 3) = 0 := by

  have h3a : g 0 = 0 := by
    specialize hg 0
    simp [hf] at hg
    linarith

  linarith [hS, h3a]