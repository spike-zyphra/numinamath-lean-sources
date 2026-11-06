import Mathlib

theorem negated_number_theory_48757 {a : ℕ} (ha : Odd a) :
    ∃ b, a ∣ 2^b - 1 := by
  use 0 
  simp at *