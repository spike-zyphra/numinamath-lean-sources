import Mathlib

theorem algebra_240214 {T : ℕ} (hT : T = Nat.sqrt ((2021 + 2021) + (2021 - 2021) + (2021 * 2021) + (2021 / 2021))) :
    IsGreatest {p | p.Prime ∧ p ∣ T} 337 := by

  have h1 : T = 2022 := by
    rw [hT]
    native_decide

  rw [h1] at *
  constructor
  · -- Show that 337 is in the set
    constructor
    · -- 337 is prime
      norm_num
    · -- 337 divides 2022
      norm_num
  · -- Show that 337 is greatest in the set
    intro p hp
    rcases hp with ⟨h2, h3⟩
    have h4 : p ≤ 2022 := by
      exact Nat.le_of_dvd (by norm_num) h3
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at h2 h3 <;> all_goals
      omega