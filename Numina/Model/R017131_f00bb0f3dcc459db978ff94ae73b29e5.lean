import Mathlib

open Real Set
open scoped BigOperators

/- If the inequality $\frac{y}{4}-{{\cos }^{2}}x\geqslant a\sin x-\frac{9}{y}$ holds for all positive real numbers $x$, $y$, then the range of the real number $a$ is ___          ___. -/
theorem inequalities_11456 (a : ℝ) :
  (∀ x > 0, ∀ y > 0, y / 4 - (cos x) ^ 2 ≥ a * sin x - 9 / y) ↔
  -3 ≤ a ∧ a ≤ 3 := by
  constructor
  · -- Assume inequality holds for all x > 0, y > 0, prove -3 ≤ a ∧ a ≤ 3
    intro h
    have h1 : -3 ≤ a := by
      have h3pi2 := h (3 * Real.pi / 2) (by linarith [Real.pi_pos]) 6 (by norm_num)
      have hsin : sin (3 * Real.pi / 2) = -1 := by 
        have h1 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
        rw [h1]
        rw [sin_add, sin_pi, cos_pi]
        norm_num
      have hcos : cos (3 * Real.pi / 2) = 0 := by 
        have h1 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
        rw [h1]
        rw [cos_add, sin_pi, cos_pi]
        norm_num
      rw [hsin, hcos] at h3pi2
      norm_num at h3pi2 
      linarith
    have h2 : a ≤ 3 := by
      have hpi2 := h (Real.pi / 2) (by linarith [Real.pi_pos]) 6 (by norm_num)
      have hsin : sin (Real.pi / 2) = 1 := by 
        apply sin_pi_div_two
      have hcos : cos (Real.pi / 2) = 0 := by 
        apply cos_pi_div_two
      rw [hsin, hcos] at hpi2
      norm_num at hpi2 
      linarith
    constructor
    · linarith 
    · linarith
  · -- Assume -3 ≤ a ∧ a ≤ 3, prove inequality holds for all x > 0, y > 0
    rintro ⟨ha1, ha2⟩
    intro x hx y hy
    have h2 : y / 4 + 9 / y ≥ 3 := by
      have h1 : y / 4 + 9 / y - 3 ≥ 0 := by
        have h2 : y > 0 := hy
        have h3 : y / 4 + 9 / y - 3 = (y ^ 2 - 12 * y + 36) / (4 * y) := by
          field_simp
          ring
        rw [h3]
        have h4 : y ^ 2 - 12 * y + 36 ≥ 0 := by 
          have h5 : (y - 6) ^ 2 ≥ 0 := sq_nonneg (y - 6)
          linarith
        have h5 : (4 * y) > 0 := by
          nlinarith
        apply div_nonneg 
        · linarith 
        · linarith
      linarith 
    have h3 : (cos x) ^ 2 + a * sin x ≤ 3 := by
      have h5 : (cos x) ^ 2 = 1 - (sin x) ^ 2 := by 
        have h1 : (cos x) ^ 2 + (sin x) ^ 2 = 1 := by 
          exact Real.cos_sq_add_sin_sq x
        linarith 
      rw [h5]
      nlinarith [sq_nonneg (sin x - 1), sq_nonneg (sin x + 1), 
        sq_nonneg (sin x - a / 2), 
        show -1 ≤ sin x by linarith [neg_one_le_sin x, sin_le_one x], 
        show sin x ≤ 1 by apply sin_le_one x, 
        show a ^ 2 ≤ 9 by nlinarith, 
        sq_nonneg (a)]
    linarith [h2, h3]