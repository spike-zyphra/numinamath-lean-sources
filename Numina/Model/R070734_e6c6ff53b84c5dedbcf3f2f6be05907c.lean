import Mathlib

theorem number_theory_90070 : ∃ n, 2006 ∣ (n ^ 3 - (2 * n + 1) ^ 2) := by
  exact ⟨361, by norm_num⟩