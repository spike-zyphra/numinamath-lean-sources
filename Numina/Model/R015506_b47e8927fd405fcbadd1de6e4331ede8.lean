import Mathlib

open Real Set
open scoped Real

theorem algebra_109560 (a : ℝ) :
  (∃ x : ℝ, sin x ^ 2 + 3 * a ^ 2 * cos x - 2 * a ^ 2 * (3 * a - 2) - 1 = 0) ↔
  -1 / 2 ≤ a ∧ a ≤ 1 := by
  constructor
  · -- Assume there exists an x satisfying the equation
    rintro ⟨x, hx⟩
    have h1 : sin x ^ 2 = 1 - cos x ^ 2 := by
      have h : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      linarith
    rw [h1] at hx
    have h2 : cos x ^ 2 - 3 * a ^ 2 * cos x + 6 * a ^ 3 - 4 * a ^ 2 = 0 := by
      nlinarith
    have h3 : (cos x - 2 * a) * (cos x - (3 * a ^ 2 - 2 * a)) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case cos x = 2 * a
      have hcos : cos x = 2 * a := by linarith
      have hcos_le : -1 ≤ cos x ∧ cos x ≤ 1 := by
        apply cos_mem_Icc
      rw [hcos] at hcos_le
      constructor
      · -- Show -1/2 ≤ a
        nlinarith
      · -- Show a ≤ 1
        nlinarith
    · -- Case cos x = 3 * a ^ 2 - 2 * a
      have hcos : cos x = 3 * a ^ 2 - 2 * a := by linarith
      have hcos_le : -1 ≤ cos x ∧ cos x ≤ 1 := by
        apply cos_mem_Icc
      rw [hcos] at hcos_le
      constructor
      · -- Show -1/2 ≤ a
        nlinarith
      · -- Show a ≤ 1
        nlinarith
  · -- Assume -1/2 ≤ a ∧ a ≤ 1
    rintro ⟨ha1, ha2⟩
    by_cases h0 : a ≤ 1 / 2
    · -- Case a ≤ 1/2
      use Real.arccos (2 * a)
      have hcos : cos (Real.arccos (2 * a)) = 2 * a := by
        apply Real.cos_arccos
        · -- Show -1 ≤ 2 * a
          nlinarith
        · -- Show 2 * a ≤ 1
          nlinarith
      have hsin2 : sin (Real.arccos (2 * a)) ^ 2 = 1 - cos (Real.arccos (2 * a)) ^ 2 := by
        have : sin (Real.arccos (2 * a)) ^ 2 + cos (Real.arccos (2 * a)) ^ 2 = 1 := Real.sin_sq_add_cos_sq (Real.arccos (2 * a))
        linarith
      rw [hcos] at hsin2
      nlinarith [hsin2, hcos, sq_nonneg (sin (Real.arccos (2 * a))), sq_nonneg (a - 1), sq_nonneg (a + 1 / 2)]
    · -- Case a > 1/2
      use Real.arccos (3 * a ^ 2 - 2 * a)
      have hcos : cos (Real.arccos (3 * a ^ 2 - 2 * a)) = 3 * a ^ 2 - 2 * a := by
        apply Real.cos_arccos
        · -- Show -1 ≤ 3 * a ^ 2 - 2 * a
          nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1 / 2)]
        · -- Show 3 * a ^ 2 - 2 * a ≤ 1
          nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1 / 2)]
      have hsin2 : sin (Real.arccos (3 * a ^ 2 - 2 * a)) ^ 2 = 1 - cos (Real.arccos (3 * a ^ 2 - 2 * a)) ^ 2 := by
        have : sin (Real.arccos (3 * a ^ 2 - 2 * a)) ^ 2 + cos (Real.arccos (3 * a ^ 2 - 2 * a)) ^ 2 = 1 := Real.sin_sq_add_cos_sq (Real.arccos (3 * a ^ 2 - 2 * a))
        linarith
      rw [hcos] at hsin2
      nlinarith [hsin2, hcos, sq_nonneg (sin (Real.arccos (3 * a ^ 2 - 2 * a))), sq_nonneg (a - 1), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2)]