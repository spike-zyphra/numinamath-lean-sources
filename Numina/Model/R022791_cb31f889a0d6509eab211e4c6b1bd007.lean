import Mathlib

theorem algebra_199854 (a : ℝ) :
    (∃ x1 x2 : ℝ, x1 ≠ x2 ∧ a^2 * (x1 - 2) + a * (39 - 20 * x1) + 20 = 0 ∧
      a^2 * (x2 - 2) + a * (39 - 20 * x2) + 20 = 0) ↔ a = 20 := by
  constructor
  · -- Assume there exist two distinct roots x1, x2, such that a^2 * (x1 - 2) + a * (39 - 20 * x1) + 20 = 0 and a^2 * (x2 - 2) + a * (39 - 20 * x2) + 20 = 0
    rintro ⟨x1, x2, hxne, he1, he2⟩
    have eq1 : a^2 * (x1 - 2) + a * (39 - 20 * x1) + 20 = 0 := he1
    have eq2 : a^2 * (x2 - 2) + a * (39 - 20 * x2) + 20 = 0 := he2
    have eq3 : a^2 * (x1 - 2) + a * (39 - 20 * x1) + 20 - (a^2 * (x2 - 2) + a * (39 - 20 * x2) + 20) = 0 := by
      linarith
    have eq4 : a^2 * (x1 - 2) - a^2 * (x2 - 2) + a * (39 - 20 * x1) - a * (39 - 20 * x2) = 0 := by
      linarith [eq3]
    have eq5 : a^2 * (x1 - x2) - 20 * a * (x1 - x2) = 0 := by
      ring_nf at eq4 ⊢
      linarith
    have eq6 : (a^2 - 20 * a) * (x1 - x2) = 0 := by
      linarith [eq5]
    cases' (mul_eq_zero.mp eq6) with h1 h2
    · -- case $a^2 - 20 * a = 0$
      have ha_eq : a * (a - 20) = 0 := by
        linarith
      cases' (mul_eq_zero.mp ha_eq) with ha0 ha20
      · -- case a = 0
        have h0 : a = 0 := by linarith
        rw [h0] at he1
        linarith
      · -- case a - 20 = 0
        have h20 : a = 20 := by linarith
        linarith
    · -- case $x1 - x2 = 0$
      have hneq : x1 = x2 := by linarith
      exfalso
      apply hxne
      linarith
  · -- Assume a = 20
    intro ha
    rw [ha]
    use 0, 1
    constructor
    · -- Show 0 ≠ 1
      norm_num
    constructor
    · -- Show 20^2 * (0 - 2) + 20 * (39 - 20 * 0) + 20 = 0
      norm_num
    · -- Show 20^2 * (1 - 2) + 20 * (39 - 20 * 1) + 20 = 0
      norm_num