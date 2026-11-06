import Mathlib

theorem number_theory_157641 (x : ℕ) (hx : x > 0) :
    ∃ f : ℕ → ℕ, (∀ i, f i > 0) ∧
      (∀ i, f i * x > 0) := by
  use (fun _ => 1)
  constructor
  · -- Show that ∀ i, f i > 0
    intro i
    simp
  · -- Show that ∀ i, f i * x > 0
    intro i
    simp
    all_goals omega