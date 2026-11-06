import Mathlib

theorem number_theory_19167 :
    IsLeast {t : ℕ | 0 < t ∧ (Nat.lcm 12 t) ^ 3 = (12 * t) ^ 2} 18 := by
  constructor
  · -- Show 18 is in the set
    constructor
    · norm_num
    · -- Verify that LCM[12, 18]^3 = (12 * 18)^2
      native_decide
  · -- Show there is no smaller element in the set
    intro t ht
    rcases ht with ⟨ht_pos, ht_eq⟩
    by_contra h
    push_neg at h
    interval_cases t <;> norm_num [Nat.lcm] at ht_eq ⊢
    <;> omega