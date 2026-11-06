import Mathlib

theorem number_theory_140281 : IsGreatest {n | 0 ≤ n ∧ 6^n ∣ 3 * 16 * 45 * 81} 4 := by
  constructor
  · -- Show that 4 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that 4 is the greatest in the set
    intro n hn
    rcases hn with ⟨hn0, hnd⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 5 := by omega
    have h2 : 6 ^ 5 ∣ (3 * 16 * 45 * 81) := by
      have h3 : 6 ^ 5 ∣ 6 ^ n := by 
        exact pow_dvd_pow _ (by linarith)
      have h4 : 6 ^ n ∣ (3 * 16 * 45 * 81) := hnd
      exact dvd_trans h3 h4
    norm_num at h2
    all_goals omega