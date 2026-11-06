import Mathlib

theorem algebra_12145 {f g : ℝ → ℝ} (hf : f = fun x => 4 - 5 * x) :
  f.invFun = fun x => (4 - x) / 5 := by
  have h1 : ∀ x, f x = 4 - 5 * x := by 
    intro x
    rw [hf]

  funext y
  have h2 : ∀ x : ℝ, f x = y ↔ x = (4 - y) / 5 := by
    intro x
    constructor
    · -- Assume f x = y, prove x = (4 - y) / 5
      intro h_eq
      rw [h1 x] at h_eq
      linarith
    · -- Assume x = (4 - y) / 5, prove f x = y
      intro h_eq
      rw [h_eq]
      rw [h1]
      all_goals
        ring
  rw [Function.invFun]
  all_goals
    simp_all [h2]