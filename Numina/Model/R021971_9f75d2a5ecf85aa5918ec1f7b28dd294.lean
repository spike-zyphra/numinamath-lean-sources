import Mathlib

theorem number_theory_308605 :
    {(x, y) : ℤ × ℤ | 5 * x ^ 2 - 6 * x * y + 7 * y ^ 2 = 130}.encard = 2 := by
  have h1 : {(x, y) : ℤ × ℤ | 5 * x ^ 2 - 6 * x * y + 7 * y ^ 2 = 130} = {(-3, -5), (3, 5)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x, y) satisfies the equation.
      rintro H
      have h2 : y ≥ -5 := by
        nlinarith [sq_nonneg (5 * x - 3 * y), sq_nonneg (x - 3), sq_nonneg (y + 5), sq_nonneg (y - 5)]
      have h3 : y ≤ 5 := by
        nlinarith [sq_nonneg (5 * x - 3 * y), sq_nonneg (x - 3), sq_nonneg (y + 5), sq_nonneg (y - 5)]
      interval_cases y <;> try { 
        have : x ≤ 10 := by nlinarith 
        have : x ≥ -10 := by nlinarith 
        interval_cases x <;> norm_num at H ⊢ <;> tauto
      }
    · -- Assume (x, y) ∈ {(-3, -5), (3, 5)}, then it satisfies the equation.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (-3, -5)
        norm_num
      · -- (3, 5)
        norm_num
  rw [h1]
  rw [Set.encard_pair]
  all_goals norm_num