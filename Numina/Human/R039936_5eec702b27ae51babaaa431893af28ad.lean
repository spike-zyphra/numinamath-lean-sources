import Mathlib

/- A bookstore is deciding what price it should charge for a certain book. After research, the store finds that if the book's price is $p$ dollars (where $p \le 32$), then the number of books sold per month is $128-4p$. What price should the store charge to maximize its revenue? -/
theorem algebra_18879 : IsMaxOn (fun (p : ℝ) ↦ (128 - 4 * p) * p) {p : ℝ | p ≤ 32} 16 := by
  refine isMaxOn_iff.mpr ?_
  intro p _
  -- complete the square
  have eq : (128 - 4 * p) * p = -(4 * (p - 16) ^ 2) + 1024 := by
    ring
  rw [eq]
  have ge : 0 ≤ (p - 16) ^ 2 := by
    exact sq_nonneg (p - 16)
  linarith