import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_69100 (a b : ℝ) (P : ℝ → ℝ)
  (hP : ∀ x, |x| ≤ 1 → |P x| ≤ 1) (hP1 : P = λ x => x^3 + a*x^2 + b*x + 1) :
  |a| + |b| ≤ 5 := by 
  have h1 := hP 1 (by norm_num)
  simp [hP1] at h1 
  have h2 := hP (-1) (by norm_num)
  simp [hP1] at h2 
  have h3 := hP (1 / 2 : ℝ) (show |(1 / 2 : ℝ)| ≤ 1 by 
    norm_num [abs_le]
  )
  simp [hP1] at h3 
  have h4 := hP (-1 / 2 : ℝ) (show |(-1 / 2 : ℝ)| ≤ 1 by 
    norm_num [abs_le]
  )
  simp [hP1] at h4 
  by_cases ha1 : a ≥ 0
  · -- Assume a ≥ 0
    by_cases hb1 : b ≥ 0
    · -- Assume a ≥ 0, b ≥ 0
      rw [abs_of_nonneg ha1, abs_of_nonneg hb1]
      cases' abs_le.mp h1 with h11 h12
      cases' abs_le.mp h2 with h21 h22
      cases' abs_le.mp h3 with h31 h32
      cases' abs_le.mp h4 with h41 h42
      all_goals
        linarith 
    · -- Assume a ≥ 0, b < 0
      rw [abs_of_nonneg ha1, abs_of_neg (lt_of_not_ge hb1)]
      cases' abs_le.mp h1 with h11 h12
      cases' abs_le.mp h2 with h21 h22
      cases' abs_le.mp h3 with h31 h32
      cases' abs_le.mp h4 with h41 h42
      all_goals
        linarith 
  · -- Assume a < 0
    by_cases hb1 : b ≥ 0
    · -- Assume a < 0, b ≥ 0
      rw [abs_of_neg (lt_of_not_ge ha1), abs_of_nonneg hb1]
      cases' abs_le.mp h1 with h11 h12
      cases' abs_le.mp h2 with h21 h22
      cases' abs_le.mp h3 with h31 h32
      cases' abs_le.mp h4 with h41 h42
      all_goals
        linarith 
    · -- Assume a < 0, b < 0
      rw [abs_of_neg (lt_of_not_ge ha1), abs_of_neg (lt_of_not_ge hb1)]
      cases' abs_le.mp h1 with h11 h12
      cases' abs_le.mp h2 with h21 h22
      cases' abs_le.mp h3 with h31 h32
      cases' abs_le.mp h4 with h41 h42
      all_goals
        linarith