import Mathlib

theorem number_theory_11689 (t : ℕ) (ht1 : t ∈ Finset.Icc 10 99) (ht2 : 11 * t ≡ 36 [MOD 100]) :
    t = 76 := by
  rw [Finset.mem_Icc] at ht1
  rcases ht1 with ⟨ht1_lower, ht1_upper⟩
  norm_num [Nat.ModEq] at ht2 
  interval_cases t <;> omega