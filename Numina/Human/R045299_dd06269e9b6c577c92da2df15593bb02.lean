import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_74101 (c : ℝ) (hc : c > 0) :
    (c ≥ 3 → IsGreatest {t | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + c * y ≤ 36 ∧ 2 * x + 3 * z ≤ 72 ∧ t = x + y + z} 36) ∧
    (c < 3 → IsGreatest {t | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + c * y ≤ 36 ∧ 2 * x + 3 * z ≤ 72 ∧ t = x + y + z} (24 + 36 / c)) := by
  constructor
  · -- First, we'll prove the case where c ≥ 3, and show that the maximum is 36.
    intro hc3
    constructor
    · -- Let's show 36 is attainable using x = 36, y = 0, z = 0
      use 36, 0, 0
      norm_num
      all_goals linarith
    · -- Now we need to show that 36 is an upper bound
      intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, h1, h2, ht⟩
      have h3 : x + c * y ≤ 36 := by linarith
      have h4 : 2 * x + 3 * z ≤ 72 := by linarith
      nlinarith [sq_nonneg (x - 36), sq_nonneg (y), sq_nonneg (z - 24), mul_self_nonneg (c - 3), hc3, hc]
  · -- Now for the second part where c < 3, and we need to show the maximum is 24 + 36/c
    intro hc3
    constructor
    · -- First, we'll show that 24 + 36/c is attainable using x = 0, y = 36/c, z = 24
      use 0, 36 / c, 24
      constructor
      · norm_num
      constructor
      · positivity
      constructor
      · norm_num
      constructor
      · -- Check constraint (1): 0 + c*(36/c) = 36 ≤ 36
        field_simp [hc.ne.symm]
      constructor
      · -- Check constraint (2): 2*0 + 3*24 = 72 ≤ 72
        norm_num
      · -- Show that t = 0 + 36/c + 24
        ring
    · -- Now we need to prove 24 + 36/c is an upper bound
      intro t ht
      rcases ht with ⟨x, y, z, hx, hy, hz, h1, h2, ht⟩
      have h3 : x + c * y ≤ 36 := by linarith
      have h4 : 2 * x + 3 * z ≤ 72 := by linarith
      have h5 : x + y + z ≤ 24 + 36 / c := by
        have h7 : c * (x + y + z) ≤ 24 * c + 36 := by
          nlinarith [sq_nonneg (x - 0), sq_nonneg (y - 36 / c), sq_nonneg (z - 24), mul_self_nonneg (c - 3), hc3, hc]
        have h8 : c * (24 + 36 / c) = 24 * c + 36 := by
          field_simp [hc.ne.symm]
          <;> ring
        nlinarith
      nlinarith [h5, hc]