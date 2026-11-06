import Mathlib

theorem algebra_17088 : IsGreatest {x | x ∣ 342 ∧ x ∣ 285} 57 := by
  constructor
  · -- Show 57 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show no greater element is in the set
    intro x hx
    rcases hx with ⟨h1, h2⟩
    have h3 : x ∣ 57 := by
      exact Nat.dvd_gcd h1 h2
    have h4 : x ≤ 57 := by
      exact Nat.le_of_dvd (by norm_num) h3
    linarith