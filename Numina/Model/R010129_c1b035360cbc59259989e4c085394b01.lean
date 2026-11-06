import Mathlib

theorem algebra_20046 {f : ℝ → ℝ} (hf : f = fun x => (3 * x + 2) / 5) :
    (Function.invFun f 4)⁻¹ = 1 / 6 := by 
  have h1 : ∀ x : ℝ, f x = (3 * x + 2) / 5 := by 
    intro x
    rw [hf]
  have h2 : ∀ (y : ℝ), f y = 4 ↔ y = 6 := by
    intro y
    constructor
    · -- Suppose \( f(y) = 4 \)
      intro h_eq
      rw [h1] at h_eq
      linarith
    · -- Suppose \( y = 6 \)
      intro h_eq
      rw [h_eq]
      rw [h1]
      norm_num
  have h3 : Function.invFun f 4 = 6 := by 
    rw [Function.invFun]
    have h4 : ∀ y : ℝ, f y = 4 ↔ y = 6 := h2
    simp_all [h4]
  rw [h3]
  all_goals norm_num