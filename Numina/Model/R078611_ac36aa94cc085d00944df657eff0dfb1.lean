import Mathlib

theorem algebra_254769 (v1 v2 v3 : ℝ) (h1 : v1 > 0) (h2 : v2 > 0) (h3 : v3 > 0)
    (h4 : 800 / v1 + 20000 / v2 + 4000 / v3 ≤ 1 * 60 + 20) (h5 : v2 = 2.5 * v3) (h6 : v3 = 3 * v1) :
    v1 ≥ 60 ∧ v2 ≥ 450 ∧ v3 ≥ 180 := by

  have h7 : v2 = 7.5 * v1 := by
    rw [h5, h6]
    ring

  have h8 : v3 = 3 * v1 := h6

  rw [show v2 = 7.5 * v1 by linarith [h7]] at h4
  rw [show v3 = 3 * v1 by linarith [h8]] at h4

  have h11 : 800 / v1 + 20000 / (7.5 * v1) + 4000 / (3 * v1) = 4800 / v1 := by
    field_simp
    ring_nf
    <;> field_simp
    <;> ring

  have h10 : 4800 / v1 ≤ (80 : ℝ) := by
    linarith [h4, h11]

  have h13 : v1 ≥ (60 : ℝ) := by
    have h14 : 4800 ≤ 80 * v1 := by
      have h15 : v1 > 0 := h1
      apply (div_le_iff₀' (by positivity : v1 > 0)).mp at h10
      linarith
    nlinarith

  have h15 : v2 ≥ 450 := by
    rw [h7]
    nlinarith [h13]

  have h16 : v3 ≥ 180 := by
    rw [h6]
    nlinarith [h13]

  constructor
  · exact h13
  constructor
  · exact h15
  · exact h16