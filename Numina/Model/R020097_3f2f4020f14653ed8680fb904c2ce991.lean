import Mathlib

theorem number_theory_11160 (p : ℕ) (hp : p.Prime) :
    (Nat.digits p 2020).sum = p + 5 ↔ p = 2 ∨ p = 107 := by 
  constructor
  · -- Forward: if the sum of the digits of 2020 in base p is p + 5, then p = 2 or 107
    intro h
    have hp2 : p ≥ 2 := Nat.Prime.two_le hp
    have h1 : p ≤ 2020 := by
      by_contra h2
      push_neg at h2
      have h2' : p ≥ 2021 := by omega
      have h3 : (Nat.digits p 2020).sum = 2020 := by
        have h4 : Nat.digits p 2020 = [2020] := by
          have h5 : 2020 < p := h2
          have h6 : Nat.digits p 2020 = [2020] := by
            simp [h5, Nat.digits_of_lt]
          exact h6
        rw [h4]
        all_goals norm_num
      rw [h3] at h
      have h4 : p = 2015 := by omega
      rw [h4] at hp
      norm_num at hp
    interval_cases p <;> norm_num at h hp <;> norm_num [Nat.Prime] at hp <;> tauto
  · -- Backward: if p = 2 or 107, then the sum of the digits of 2020 in base p is p + 5
    rintro (h | h)
    · -- p = 2
      rw [h]
      native_decide
    · -- p = 107
      rw [h]
      native_decide