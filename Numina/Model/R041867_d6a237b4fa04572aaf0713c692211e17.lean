import Mathlib

open Real Set
open scoped Real

theorem calculus_16539 (x : ℝ) :
  cos x / (1 + sin x) + (1 + sin x) / cos x = 2 * 1 / cos x := by 
  by_cases h1 : 1 + sin x = 0
  · -- case where 1 + sin x = 0
    have h2 : sin x = -1 := by linarith
    have h3 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    rw [h2] at h3
    have h4 : cos x ^ 2 = 0 := by nlinarith
    have h5 : cos x = 0 := by
      nlinarith
    simp [h1, h5]
    all_goals try { nlinarith }
  · -- case where 1 + sin x ≠ 0
    by_cases h2 : cos x = 0
    · -- case where cos x = 0
      have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
      rw [h2] at h3
      have h4 : sin x ^ 2 = 1 := by nlinarith
      have h5 : sin x = 1 ∨ sin x = -1 := by
        rw [sq_eq_one_iff] at h4
        tauto
      cases h5 with
      | inl h6 =>
        simp [h2, h6]
        all_goals try { nlinarith }
      | inr h7 =>
        exfalso
        apply h1
        linarith
    · -- case where both 1 + sin x ≠ 0 and cos x ≠ 0
      have h6 : cos x / (1 + sin x) + (1 + sin x) / cos x = (cos x ^ 2 + (1 + sin x) ^ 2) / (cos x * (1 + sin x)) := by
        field_simp [(show 1 + sin x ≠ 0 by assumption), h2]
        <;> ring_nf
        <;> field_simp [(show 1 + sin x ≠ 0 by assumption), h2]
        <;> ring
      rw [h6]
      have h7 : cos x ^ 2 + (1 + sin x) ^ 2 = 2 * (1 + sin x) := by
        have h8 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        nlinarith [sq_nonneg (sin x + 1), sq_nonneg (cos x)]
      rw [h7]
      have h8 : cos x * (1 + sin x) ≠ 0 := by
        apply mul_ne_zero
        · -- cos x ≠ 0
          exact h2
        · -- 1 + sin x ≠ 0
          exact h1
      have h9 : (2 * (1 + sin x)) / (cos x * (1 + sin x)) = 2 / cos x := by
        have h10 : cos x * (1 + sin x) = cos x * (1 + sin x) := by
          rfl
        have h13 : cos x * (1 + sin x) ≠ 0 := h8
        have h14 : 1 + sin x ≠ 0 := h1
        field_simp [h13, h2, h14]
        <;> ring_nf
        <;> field_simp [h13, h2, h14]
        all_goals nlinarith
      rw [h9]
      all_goals try { field_simp [h1, h2] }
      <;> ring_nf <;> field_simp [h1, h2]
      <;> nlinarith
      all_goals try { nlinarith }