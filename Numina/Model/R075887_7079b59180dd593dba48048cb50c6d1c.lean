import Mathlib

open Finset Real

theorem number_theory_214424 {R : ℝ} (hR : R > 0.5) :
    ∃ n : ℕ, ∃ s : Finset ℝ,
      s.card = n ∧
      (∀ x ∈ s, x > 0) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → x / y > R) := by

  use 0
  use ∅
  all_goals simp_all