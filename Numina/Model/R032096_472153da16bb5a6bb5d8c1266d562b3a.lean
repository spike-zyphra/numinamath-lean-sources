import Mathlib

theorem algebra_758 (h : ℝ → ℝ) (ht : h = fun t => 45 - 7 * t - 6 * t ^ 2) :
    0 ≤ t ∧ h t = 25 ↔ t = 4 / 3 := by
  constructor
  · -- Assume 0 ≤ t ∧ h t = 25, prove t = 4 / 3
    rintro ⟨ht_nonneg, heq⟩
    have eq1 : h t = 45 - 7 * t - 6 * t ^ 2 := by
      rw [ht]
    rw [eq1] at heq
    have eq2 : 6 * t ^ 2 + 7 * t - 20 = 0 := by
      nlinarith
    have eq3 : (t - 4 / 3) * (6 * t + 15) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq3) with eq4 eq5
    · -- t - 4/3 = 0
      linarith
    · -- 6t + 15 = 0
      nlinarith
  · -- Assume t = 4/3, prove 0 ≤ t ∧ h t = 25
    intro heq
    have ht_nonneg : 0 ≤ t := by
      nlinarith [heq]
    have heq25 : h t = 25 := by
      rw [ht]
      rw [heq]
      norm_num
    constructor
    · exact ht_nonneg
    · exact heq25