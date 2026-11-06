import Mathlib

theorem number_theory_277948 : IsGreatest {x | 4 ∣ x ∧ x < 100} 96 := by
  constructor
  · -- Proving 96 belongs to the set
    exact ⟨by norm_num, by norm_num⟩
  · -- Proving no greater element exists in the set
    intro x hx
    have ⟨hx1, hx2⟩ := hx
    have : x ≤ 96 := by
      omega
    linarith