import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10902 {a : ℝ} (ha : 0 ≤ a) :
    IsLeast {z : ℝ | ∃ x y, (x - 4 * y + 3 ≤ 0 ∧ 3 * x + 5 * y - 25 ≤ 0 ∧ x - a ≥ 0) ∧ z = (x * 2 + y * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2))} 2 ↔ a = 2 := by 
  constructor
  · -- Assume 2 is the least element
    intro h
    have h1 : 2 ∈ {z : ℝ | ∃ x y, (x - 4 * y + 3 ≤ 0 ∧ 3 * x + 5 * y - 25 ≤ 0 ∧ x - a ≥ 0) ∧ z = (x * 2 + y * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2))} := by
      have h2 : IsLeast {z : ℝ | ∃ x y, (x - 4 * y + 3 ≤ 0 ∧ 3 * x + 5 * y - 25 ≤ 0 ∧ x - a ≥ 0) ∧ z = (x * 2 + y * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2))} 2 := h
      exact h2.1
    rcases h1 with ⟨x, y, ⟨h1, h2, h3⟩, h4⟩
    have h5 : (x * 2 + y * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2)) = x := by
      have h6 : Real.sqrt (2 ^ 2 + 0 ^ 2) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h6]
      <;> field_simp
      <;> ring
    have h6 : x = 2 := by
      linarith [h4, h5]
    have h7 : ∀ z, z ∈ {z : ℝ | ∃ x y, (x - 4 * y + 3 ≤ 0 ∧ 3 * x + 5 * y - 25 ≤ 0 ∧ x - a ≥ 0) ∧ z = (x * 2 + y * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2))} → 2 ≤ z := by
      have h8 : IsLeast {z : ℝ | ∃ x y, (x - 4 * y + 3 ≤ 0 ∧ 3 * x + 5 * y - 25 ≤ 0 ∧ x - a ≥ 0) ∧ z = (x * 2 + y * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2))} 2 := h
      have h9 : ∀ z ∈ {z : ℝ | ∃ x y, (x - 4 * y + 3 ≤ 0 ∧ 3 * x + 5 * y - 25 ≤ 0 ∧ x - a ≥ 0) ∧ z = (x * 2 + y * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2))}, 2 ≤ z := h8.2
      exact h9
    have h8 : a ∈ {z : ℝ | ∃ x y, (x - 4 * y + 3 ≤ 0 ∧ 3 * x + 5 * y - 25 ≤ 0 ∧ x - a ≥ 0) ∧ z = (x * 2 + y * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2))} := by
      use a, (25 - 3 * a) / 5
      constructor
      · -- Check constraints
        constructor
        · -- First constraint
          nlinarith
        constructor
        · -- Second constraint
          nlinarith
        · -- Third constraint
          linarith
      · -- Show z = a
        have h10 : (a * 2 + (25 - 3 * a) / 5 * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2)) = a := by
          have h6 : Real.sqrt (2 ^ 2 + 0 ^ 2) = (2 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            <;> ring_nf <;> norm_num
          rw [h6]
          field_simp
          <;> ring
        linarith [h10]
    have h9 : 2 ≤ a := by
      apply h7 a h8
    have h10 : a ≤ 2 := by
      nlinarith
    linarith
  · -- Assume a = 2
    intro ha_eq
    rw [ha_eq] at *
    constructor
    · -- Show that 2 is in the set
      use 2, 2
      constructor
      · -- Check constraints
        constructor
        · -- First constraint
          norm_num
        constructor
        · -- Second constraint
          norm_num
        · -- Third constraint
          norm_num
      · -- Show z = 2
        have h5 : (2 * 2 + (2 : ℝ) * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2)) = (2 : ℝ) := by
          have h6 : Real.sqrt (2 ^ 2 + 0 ^ 2) = (2 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            <;> ring_nf <;> norm_num
          rw [h6]
          <;> field_simp
          <;> ring
        linarith [h5]
    · -- Show that 2 is minimal
      intro z hz
      rcases hz with ⟨x, y, ⟨h1, h2, h3⟩, h4⟩
      have h5 : (x * 2 + y * 0) / (Real.sqrt (2 ^ 2 + 0 ^ 2)) = x := by
        have h6 : Real.sqrt (2 ^ 2 + 0 ^ 2) = (2 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        rw [h6]
        <;> field_simp
        <;> ring
      have h6 : 2 ≤ x := by
        nlinarith
      nlinarith [h4, h5, h6]