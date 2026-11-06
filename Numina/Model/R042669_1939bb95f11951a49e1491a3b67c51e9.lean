import Mathlib

open Real

theorem other_76127 {p : ℝ → ℝ} (hp : p = fun x => x ^ 2 - x + 1)
    (α : ℝ) (hα : p (p (p (p α))) = 0) :
    (p α - 1) * p α * p (p α) * p (p (p α)) = -1 := by
  have h1 : ∀ (x : ℝ), p x = x ^ 2 - x + 1 := by 
    intro x
    rw [hp]
  have h6 : p (p (p (p α))) ≥ 3 / 4 := by
    have h7 : ∀ (x : ℝ), p x ≥ 3 / 4 := by
      intro x
      have h8 : p x = x ^ 2 - x + 1 := by 
        apply h1
      rw [h8]
      nlinarith [sq_nonneg (x - 1 / 2)]
    specialize h7 (p (p (p α)))
    linarith
  linarith [hα, h6]