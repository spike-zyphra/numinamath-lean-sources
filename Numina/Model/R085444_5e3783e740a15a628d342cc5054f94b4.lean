import Mathlib

theorem algebra_266742 (α β : ℝ × ℝ) (h₁ : α ≠ 0) (h₂ : β ≠ 0)
    (h₃ : Real.sqrt ((α.1 + β.1)^2 + (α.2 + β.2)^2) =
      Real.sqrt ((α.1 - β.1)^2 + (α.2 - β.2)^2)) :
    α.1 * β.1 + α.2 * β.2 = 0 := by
  have h4 : (α.1 + β.1) ^ 2 + (α.2 + β.2) ^ 2 = (α.1 - β.1) ^ 2 + (α.2 - β.2) ^ 2 := by
    rw [Real.sqrt_inj (by positivity) (by positivity) ] at h₃
    linarith
  have eq2 : (α.1 + β.1) ^ 2 = α.1^2 + 2 * (α.1 * β.1) + β.1^2 := by ring
  have eq3 : (α.2 + β.2) ^ 2 = α.2^2 + 2 * (α.2 * β.2) + β.2^2 := by ring
  have eq4 : (α.1 - β.1) ^ 2 = α.1^2 - 2 * (α.1 * β.1) + β.1^2 := by ring
  have eq5 : (α.2 - β.2) ^ 2 = α.2^2 - 2 * (α.2 * β.2) + β.2^2 := by ring
  rw [eq2, eq3, eq4, eq5] at h4
  linarith