import Mathlib

theorem algebra_287990 :
  {y : ℝ | ∃ x : ℝ, 0 < x ∧ (1 - 10 / 100) * x = (1 - 20 / 100) * y} =
  {y : ℝ | ∃ x : ℝ, 0 < x ∧ y = 1.125 * x} := by
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · -- First direction: {y | ∃ x > 0, 0.9x = 0.8y} → {y | ∃ x > 0, y = 1.125x}
    rintro ⟨x, hx, h⟩
    refine ⟨x, hx, ?_⟩
    have h1 : (1 - 10 / 100 : ℝ) = 0.9 := by norm_num
    have h2 : (1 - 20 / 100 : ℝ) = 0.8 := by norm_num
    rw [h1, h2] at h
    have h3 : y = 1.125 * x := by
      ring_nf at h ⊢
      linarith
    linarith
  · -- Second direction: {y | ∃ x > 0, y = 1.125x} → {y | ∃ x > 0, 0.9x = 0.8y}
    rintro ⟨x, hx, h⟩
    refine ⟨x, hx, ?_⟩
    have h1 : (1 - 10 / 100 : ℝ) = 0.9 := by norm_num
    have h2 : (1 - 20 / 100 : ℝ) = 0.8 := by norm_num
    rw [h1, h2, show y = (1.125 : ℝ) * x by linarith [h]]
    ring_nf