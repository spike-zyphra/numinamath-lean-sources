import Mathlib

theorem algebra_14670 (A B C D E : ℝ × ℝ)
    (h₀ : A = (0, 10)) (h₁ : B = (0, 0)) (h₂ : C = (10, 0))
    (h₃ : D = (10, 10)) (h₄ : E = (6.4, 5.2)) (h₅ : dist A E = 8)
    (h₆ : dist D E = 6) :
    (MeasureTheory.volume (convexHull ℝ {A, E, D, C, B})).toReal = 76 := by
  rw [h₀] at *
  rw [h₁] at *
  rw [h₂] at *
  rw [h₃] at *
  rw [h₄] at *
  norm_num [dist_eq_norm, Prod.norm_def] at h₅ h₆ ⊢
  <;> norm_num [Set.mem_insert_iff, Set.mem_singleton_iff, convexHull_insert, convexHull_singleton, MeasureTheory.Measure.toReal_atLeast_iff] at h₅ h₆ ⊢
  <;> linarith