import Mathlib

theorem algebra_201513 (x : ℕ → ℝ) (h₀ : x 0 = 1) (h₁ : x 1 = 1) (h₂ : x 2 = -1)
    (h₃ : ∀ n, x (n + 3) = x (n + 2) * x n) :
    x 2021 = 1 := by
  have eq5 : ∀ (n : ℕ), x (7 * n) = 1 ∧ x (7 * n + 1) = 1 ∧ x (7 * n + 2) = -1 ∧ x (7 * n + 3) = -1 ∧ x (7 * n + 4) = -1 ∧ x (7 * n + 5) = 1 ∧ x (7 * n + 6) = -1 := by 
    intro n
    induction n with
    | zero =>
      constructor
      · norm_num [h₀]
      constructor
      · norm_num [h₁]
      constructor
      · norm_num [h₂]
      constructor
      · norm_num [h₃, h₀, h₁, h₂]
      constructor
      · norm_num [h₃, h₀, h₁, h₂]
      constructor
      · norm_num [h₃, h₀, h₁, h₂]
      · norm_num [h₃, h₀, h₁, h₂]
    | succ n ih =>
      have eq1 : 7 * (n + 1) = 7 * n + 7 := by omega
      rw [eq1] at *
      rcases ih with ⟨h₀', h₁', h₂', h₃', h₄', h₅', h₆'⟩
      constructor
      · -- Show that x (7 * n + 7) = 1
        norm_num [h₃, h₀', h₁', h₂', h₃', h₄', h₅', h₆']
        <;> linarith
      constructor
      · -- Show that x (7 * n + 8) = 1
        norm_num [h₃, h₀', h₁', h₂', h₃', h₄', h₅', h₆']
        <;> linarith
      constructor
      · -- Show that x (7 * n + 9) = -1
        norm_num [h₃, h₀', h₁', h₂', h₃', h₄', h₅', h₆']
        <;> linarith
      constructor
      · -- Show that x (7 * n + 10) = -1
        norm_num [h₃, h₀', h₁', h₂', h₃', h₄', h₅', h₆']
        <;> linarith
      constructor
      · -- Show that x (7 * n + 11) = -1
        norm_num [h₃, h₀', h₁', h₂', h₃', h₄', h₅', h₆']
        <;> linarith
      constructor
      · -- Show that x (7 * n + 12) = 1
        norm_num [h₃, h₀', h₁', h₂', h₃', h₄', h₅', h₆']
        <;> linarith
      · -- Show that x (7 * n + 13) = -1
        norm_num [h₃, h₀', h₁', h₂', h₃', h₄', h₅', h₆']
        <;> linarith
  have h5 := (eq5 288).2.2.2.2.2.1
  norm_num at h5 ⊢
  all_goals linarith