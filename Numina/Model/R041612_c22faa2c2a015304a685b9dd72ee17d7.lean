import Mathlib

theorem number_theory_291778 : ¬ ∀ n : ℕ, Nat.Prime (2^(2*n+1) - 1) := by
  intro h
  have h4 := h 4
  norm_num at h4