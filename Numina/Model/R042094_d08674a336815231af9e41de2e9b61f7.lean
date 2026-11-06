import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_104344 {f : ℝ → ℝ} (hf : f = λ x => sin (2 * x) * cos x / (1 - sin x)) :
    ∀ x, x ∉ {x | ∃ k : ℤ, x = 2 * k * π + π / 2} → f x ∈ Ico (-1 / 2) 4 := by
  intro x hx
  have h1 : f x = sin (2 * x) * cos x / (1 - sin x) := by 
    rw [hf]
  rw [h1]
  have h2 : sin x ≠ 1 := by
    by_contra h
    have h3 : x ∈ {x | ∃ k : ℤ, x = 2 * k * π + π / 2} := by
      have h4 : sin x = 1 := h
      obtain ⟨k, hk⟩ := Real.sin_eq_one_iff.1 h4
      refine ⟨k, by linarith⟩
    contradiction
  have h3 : sin (2 * x) * cos x / (1 - sin x) = 2 * sin x * (1 + sin x) := by
    have h4 : sin (2 * x) = 2 * sin x * cos x := by
      rw [sin_two_mul]
    rw [h4]
    have h5 : cos x ^ 2 = 1 - sin x ^ 2 := by
      have h6 : cos x ^ 2 + sin x ^ 2 = 1 := by
        exact Real.cos_sq_add_sin_sq x
      linarith
    have h6 : 1 - sin x ≠ 0 := by
      intro h7
      have h7 : sin x = 1 := by linarith
      tauto
    have h7 : (2 * sin x * cos x) * cos x = 2 * sin x * (1 - sin x ^ 2) := by
      calc 
        (2 * sin x * cos x) * cos x = 2 * sin x * cos x ^2 := by ring
        _ = 2 * sin x * (1 - sin x ^2) := by 
          rw [h5]
    have h8 : 2 * sin x * (1 - sin x ^ 2) = 2 * sin x * (1 - sin x) * (1 + sin x) := by 
      ring
    rw [h7, h8]
    field_simp [h6]
    <;> ring
  rw [h3]
  constructor
  · -- Show that $f(x) \geq -\frac{1}{2}$
    nlinarith [sq_nonneg (sin x + 1 / 2)]
  · -- Show that $f(x) < 4$
    have h7 : sin x ≤ 1 := by
      linarith [Real.sin_le_one x]
    have h8 : -1 ≤ sin x := by
      linarith [Real.neg_one_le_sin x]
    nlinarith [sq_nonneg (sin x + 2), sq_nonneg (sin x - 1),
      Real.sin_sq_add_cos_sq x, sq_pos_of_ne_zero (show 1 - sin x ≠ 0 by 
        intro h7'
        have : sin x = 1 := by linarith
        tauto
      )
    ]