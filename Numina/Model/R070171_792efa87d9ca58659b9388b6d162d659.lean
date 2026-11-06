import Mathlib

theorem number_theory_2975 : IsGreatest {r | 0 < r ∧ (3^r : ℤ) ∣ 4^15 - 1} 2 := by 
  constructor
  · -- Show that 2 is in the set
    constructor
    · -- Show that 2 is positive
      norm_num 
    · -- Show that 3^2 divides 4^15 - 1
      norm_num
  · -- Show that 2 is the greatest element in the set
    intro r hr
    rcases hr with ⟨hr_pos, hr_div⟩
    by_contra h
    push_neg at h
    have h3 : r ≥ 3 := by omega
    have h4 : ¬ (3 ^ 3 : ℤ) ∣ (4^15 - 1 : ℤ) := by
      norm_num
    have h5 : (3 : ℤ) ^ r ∣ (4^15 - 1 : ℤ) := hr_div
    have h6 : (3 : ℤ) ^ 3 ∣ (4^15 - 1 : ℤ) := by
      have h7 : (3 : ℤ) ^ 3 ∣ (3 : ℤ) ^ r := by
        exact pow_dvd_pow _ (by omega)
      exact dvd_trans h7 hr_div
    have h8 : ¬ (3 ^ 3 : ℤ) ∣ (4^15 - 1 : ℤ) := h4
    contradiction