import Mathlib

open Real

theorem inequalities_316254 (a : ℝ) (ha : a ≠ 0) :
    (a^2 > 0 → ∀ x y, a^2 * x > a^2 * y → x > y) ∧
    (a^2 ≥ 0 → ∀ x y, a^2 * x ≥ a^2 * y → x ≥ y) ∧
    (a^2 ≠ 0 → ∀ x y, x / a^2 ≥ y / a^2 → x ≥ y) ∧
    (a^2 ≠ 0 → ∀ x y, x ≥ y → x / a^2 ≥ y / a^2) := by
  constructor
  · -- Proof for proposition 1: If a^2 x > a^2 y, then x > y given a^2 > 0
    intro ha1 x y h
    have h1 : a^2 > 0 := by
      have h3 : a ≠ 0 := ha
      have : a^2 > 0 := by
        exact sq_pos_of_ne_zero (show a ≠ 0 by exact h3)
      assumption
    have h2 : x > y := by
      nlinarith
    exact h2
  constructor
  · -- Proof for proposition 2: If a^2 x ≥ a^2 y, then x ≥ y given a^2 ≥ 0
    intro ha2 x y h
    have h1 : a^2 > 0 := by
      have h3 : a ≠ 0 := ha
      have : a^2 > 0 := by
        exact sq_pos_of_ne_zero (show a ≠ 0 by exact h3)
      assumption
    have h2 : x ≥ y := by
      nlinarith
    exact h2
  constructor
  · -- Proof for proposition 3: If x/a^2 ≥ y/a^2, then x ≥ y given a^2 ≠ 0
    intro ha3 x y h
    have h1 : a^2 > 0 := by
      have h3 : a ≠ 0 := ha
      have : a^2 > 0 := by
        exact sq_pos_of_ne_zero (show a ≠ 0 by exact h3)
      assumption
    have h2 : x ≥ y := by
      have h3 : x / a^2 ≥ y / a^2 := h
      have h4 : x ≥ y := by
        have pos1 : a^2 > 0 := h1
        have h5 : x ≥ y := by
          have h6 : x / a^2 ≥ y / a^2 := h
          have h7 : x = (x / a^2) * a^2 := by
            field_simp [show a ≠ 0 by exact ha]
          have h8 : y = (y / a^2) * a^2 := by
            field_simp [show a ≠ 0 by exact ha]
          nlinarith
        assumption
      assumption
    exact h2
  · -- Proof for proposition 4: If x ≥ y, then x/a^2 ≥ y/a^2 given a^2 ≠ 0
    intro ha4 x y h
    have h1 : a^2 > 0 := by
      have h3 : a ≠ 0 := ha
      have : a^2 > 0 := by
        exact sq_pos_of_ne_zero (show a ≠ 0 by exact h3)
      assumption
    have h4 : x / a^2 ≥ y / a^2 := by
      have h3 : x ≥ y := h
      have pos1 : a^2 > 0 := h1
      have h4 : x / a^2 ≥ y / a^2 := by
        apply (div_le_div_right pos1).mpr
        linarith
      assumption
    exact h4