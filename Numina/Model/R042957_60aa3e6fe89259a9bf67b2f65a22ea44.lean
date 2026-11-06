import Mathlib

theorem number_theory_262451 : ∃ x y z w v : ℕ, x * 16 + y * 17 + z * 23 + w * 39 + v * 40 = 100 := by
  exact ⟨2, 4, 0, 0, 0, by norm_num⟩