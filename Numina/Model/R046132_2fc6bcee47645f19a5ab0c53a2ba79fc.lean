import Mathlib

theorem algebra_607519 :
  { (x, y) : ℤ × ℤ | x ^ 3 + y ^ 3 = (x + y) ^ 2 } = { (2, 2), (1, 2), (1, 0), (2, 1), (0, 1) } ∪ { (x, -x) | x : ℤ } := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- First direction: if (x, y) satisfies the equation, then it's in the union.
    rintro H
    have h1 : x ^ 3 + y ^ 3 = (x + y) ^ 2 := by
      nlinarith
    have h2 : (x + y) * (x ^ 2 - x * y + y ^ 2 - (x + y)) = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    cases (mul_eq_zero.mp h2) with
    | inl h3 =>
      have hy : y = -x := by linarith
      right
      simp [hy]
    | inr h3 =>
      have h3 : x ^ 2 - x * y + y ^ 2 = x + y := by linarith
      have h4 : y ≤ 3 := by
        nlinarith [sq_nonneg (y - 2), sq_nonneg (x - 2), sq_nonneg (y - x), sq_nonneg (y - 1), sq_nonneg (x - 1)]
      have h5 : y ≥ -2 := by
        nlinarith [sq_nonneg (y + 1), sq_nonneg (x + 1), sq_nonneg (y - x), sq_nonneg (y - 1), sq_nonneg (x - 1)]
      interval_cases y <;> try { 
        have : x ≤ 3 := by nlinarith
        have : x ≥ -2 := by nlinarith
        interval_cases x <;> norm_num at h3 ⊢ <;> tauto 
      }
  · -- Second direction: if (x, y) is in the union, then it satisfies the equation.
    rintro (h | h)
    · -- First case: (x, y) is in the finite set.
      rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
        norm_num
    · -- Second case: (x, y) is in the set of (x, -x).
      rcases h with ⟨x, rfl⟩
      ring