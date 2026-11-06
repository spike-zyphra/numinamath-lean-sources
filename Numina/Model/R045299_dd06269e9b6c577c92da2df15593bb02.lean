import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_74101 (c : ℝ) (hc : c > 0) :
    (c ≥ 3 → IsGreatest {t | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + c * y ≤ 36 ∧ 2 * x + 3 * z ≤ 72 ∧ t = x + y + z} 36) ∧
    (c < 3 → IsGreatest {t | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ x + c * y ≤ 36 ∧ 2 * x + 3 * z ≤ 72 ∧ t = x + y + z} (24 + 36 / c)) := by
  constructor
  · -- First part: if c ≥ 3, prove that 36 is the greatest.
    intro hc3
    constructor
    · -- Show that (36, 0, 0) is in the set.
      use 36, (0 : ℝ), (0 : ℝ)
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · linarith
      constructor
      · linarith
      all_goals norm_num
    · -- Show that 36 is the greatest.
      intro t ht
      rcases ht with ⟨x, y, z, hx1, hy1, hz1, h1, h2, h_eq⟩
      nlinarith
  · -- Second part: if c < 3, prove that 24 + 36/c is the greatest.
    intro hc2
    constructor
    · -- Show that (0, 36/c, 24) is in the set.
      use (0 : ℝ), (36 / c : ℝ), (24 : ℝ)
      constructor
      · norm_num
      constructor
      · -- Show that 36/c ≥ 0 by positivity of c.
        have hc2' : c > 0 := hc
        positivity
      constructor
      · norm_num
      constructor
      · -- Show that the first constraint is satisfied.
        field_simp
        <;> nlinarith
      constructor
      · -- Show that the second constraint is satisfied.
        norm_num
      · -- Show that t = 0 + 36/c + 24.
        field_simp
        <;> linarith
    · -- Show that 24 + 36/c is the greatest.
      intro t ht
      rcases ht with ⟨x, y, z, hx1, hy1, hz1, h1, h2, h_eq⟩
      have h6 : x + y + z ≤ 24 + 36 / c := by
        have h1' : c * (x + y + z) ≤ 24 * c + 36 := by
          have hc3' : c < 3 := hc2
          nlinarith [sq_nonneg (x - 0), sq_nonneg (y - 36 / c), sq_nonneg (z - 24),
            mul_pos hc (show 0 < (3 - c) by linarith),
            mul_pos hc (show 0 < c by linarith)]
        have h12 : (24 * c + 36) / c = 24 + 36 / c := by
          field_simp
          <;> ring
        have h11 : (x + y + z) ≤ (24 * c + 36) / c := by
          have h13 : c * (x + y + z) ≤ 24 * c + 36 := h1'
          apply (le_div_iff₀ (by linarith)).mpr
          linarith
        linarith [h11, h12]
      linarith