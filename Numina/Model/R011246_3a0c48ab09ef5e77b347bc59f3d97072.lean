import Mathlib

theorem algebra_99437 {α : ℝ} (h : α^5 - α^3 + α - 2 = 0) : ⌊α^6⌋ = 3 := by
  have h2 : α ^ 5 = α ^ 3 - α + 2 := by linarith
  have hα1 : α ≥ 1 := by
    nlinarith [sq_nonneg (α ^ 2 - 1), sq_nonneg (α - 1), sq_nonneg (α + 1), sq_nonneg (α^2 - α), sq_nonneg (α ^ 2 - (α + 1)), sq_nonneg (α ^ 2 + α - 2), sq_nonneg ((α^2 - α)^2) ]
  have hα2 : α < 2 := by
    nlinarith [sq_nonneg (α ^ 2 - 1.44), sq_nonneg (α - 2), sq_nonneg (α ^ 2 - 2 * α), sq_nonneg (α ^ 2 - 4), sq_nonneg (α ^ 2 - 1), sq_nonneg ((α - 2)^2 ), hα1, sq_nonneg ((α^2 -1)^2), sq_nonneg (α^3-8) ]
  have h3 : 3 ≤ α ^ 6 := by
    nlinarith [sq_nonneg (α ^ 3 - 2), sq_nonneg (α ^ 3 - α ^ 2), sq_nonneg (α ^ 2 - 1), sq_nonneg ((α ^ 2 - 1.21 )^2 ), hα1 ]
  have h4 : α ^ 6 < 4 := by
    nlinarith [sq_nonneg (α ^ 3 - 2), sq_nonneg (α ^ 3 - α ^ 2), sq_nonneg (α ^ 2 - 1.44), sq_nonneg (α - 2), hα2 ]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> nlinarith