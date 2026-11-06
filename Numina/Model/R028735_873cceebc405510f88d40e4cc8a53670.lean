import Mathlib

theorem inequalities_48392 : { a | ∀ x y : ℝ, 3 * x ^ 2 + y ^ 2 ≥ -a * x * (x + y) } = { a | -2 ≤ a ∧ a ≤ 6 } := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume h, prove a ∈ [-2, 6]
    intro h
    have h1 := h 1 1
    have h2 := h (-1) 2
    have h3 := h 1 (-3)
    have h4 := h (-2) 1
    have h9 : -2 ≤ a := by
      nlinarith 
    have h10 : a ≤ 6 := by
      nlinarith 
    tauto
  · -- Assume a ∈ [-2, 6], prove h
    rintro ⟨ha1, ha2⟩
    intro x y
    have h5 : 3 * x ^ 2 + y ^ 2 ≥ -a * x * (x + y) := by
      nlinarith [sq_nonneg (y + a * x / 2), sq_nonneg (y - a * x * (1 / 2)), sq_nonneg (y + (3 : ℝ) * x), sq_nonneg ((y) - (a + 2) * x), sq_nonneg ((y) + (a + 2) * x), sq_nonneg ((6 - a) * x - (a + 2) * y), sq_nonneg ((a + 2) * x - (6 - a) * y), sq_nonneg ((a + 2) * x * (y)), sq_nonneg ((6 - a) * x * (y)), sq_nonneg ((a + 2) * x - y), sq_nonneg ((6 - a) * x - y), sq_nonneg ((a + 2) * x + (6 - a) * y), sq_nonneg (x * (y)), sq_nonneg (a * x - y * (1 / 2)), sq_nonneg (a * x * (1 / 2) - y), sq_nonneg (3 * x - y), sq_nonneg (3 * x + y), sq_nonneg (x * (a - 6)), sq_nonneg (y * (a - 6)), mul_nonneg (show 0 ≤ a + 2 by linarith) (show 0 ≤ 6 - a by linarith)]
    linarith