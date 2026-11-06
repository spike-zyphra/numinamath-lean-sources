import Mathlib

/- If the coordinates $x$ and $y$ of a point $(x,y)$ are integers, then the point is called a lattice point. How many lattice points are there in the region defined by $ y \geq 5 x ^ { 2 } - 1 0 x + 2 3 $ and $ y \leq 3 x ^ { 2 } + 1 3 x + 3 6 \ $?

If the coordinates $x$ and $y$ of a point $(x,y)$ are integers, then the point is called a lattice point. How many lattice points are there in the region defined by $ y \geq 5 x ^ { 2 } - 1 0 x + 2 3 $ and $ y \leq 3 x ^ { 2 } + 1 3 x + 3 6 $? -/
theorem algebra_13269 :
    Set.ncard {p : ℤ × ℤ | p.2 ≥ 5 * p.1 ^ 2 - 10 * p.1 + 23 ∧ p.2 ≤ 3 * p.1 ^ 2 + 13 * p.1 + 36} = 676 := by
  have h2 : {p : ℤ × ℤ | p.2 ≥ 5 * p.1 ^ 2 - 10 * p.1 + 23 ∧ p.2 ≤ 3 * p.1 ^ 2 + 13 * p.1 + 36} = Finset.filter (fun p : ℤ × ℤ => p.2 ≥ 5 * p.1 ^ 2 - 10 * p.1 + 23 ∧ p.2 ≤ 3 * p.1 ^ 2 + 13 * p.1 + 36) (Finset.Icc (0 : ℤ) 12 ×ˢ Finset.Icc (0 : ℤ) 624) := by
    ext ⟨x, y⟩
    simp
    intro h1 h2
    have h3 : x ≥ 0 := by
      nlinarith [sq_nonneg (x * 10), sq_nonneg ((2 * x - 1)), sq_nonneg (x - 12), sq_nonneg (y - 3 * x ^ 2 - 13 * x - 36), sq_nonneg (y - 5 * x ^ 2 + 10 * x - 23)]
    have h4 : x ≤ 12 := by
      nlinarith [sq_nonneg (x * 10), sq_nonneg ((2 * x - 1)), sq_nonneg (x - 12), sq_nonneg (y - 3 * x ^ 2 - 13 * x - 36), sq_nonneg (y - 5 * x ^ 2 + 10 * x - 23)]
    have h5 : y ≥ 0 := by
      nlinarith [sq_nonneg (x * 10), sq_nonneg ((2 * x - 1)), sq_nonneg (x - 12), sq_nonneg (y - 3 * x ^ 2 - 13 * x - 36), sq_nonneg (y - 5 * x ^ 2 + 10 * x - 23)]
    have h6 : y ≤ 624 := by
      nlinarith [sq_nonneg (x * 10), sq_nonneg ((2 * x - 1)), sq_nonneg (x - 12), sq_nonneg (y - 3 * x ^ 2 - 13 * x - 36), sq_nonneg (y - 5 * x ^ 2 + 10 * x - 23)]
    tauto
  rw [h2]
  rw [Set.ncard_coe_Finset]
  native_decide