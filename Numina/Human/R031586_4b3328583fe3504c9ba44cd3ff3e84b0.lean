import Mathlib

theorem algebra_15576 : IsLeast {n : ℝ | ∃ x y, n = x ^ 2 + x * y + y ^ 2} 0 := by
  constructor
  · -- Let's tackle the first part. We need to prove that 0 belongs to this set.
    use 0, 0
    norm_num
  · -- Now for the second part. We need to prove that no negative value belongs to this set.
    intro n hn
    rcases hn with ⟨x, y, h⟩
    have h1 : n = (x + y / 2) ^ 2 + (3 / 4) * y ^ 2 := by
      linarith [h]
    have h2 : n ≥ 0 := by 
      rw [h1]
      have h3 : (3 / 4) * y ^ 2 ≥ 0 := mul_nonneg (by norm_num) (sq_nonneg y)
      have h4 : (x + y / 2) ^ 2 ≥ 0 := sq_nonneg (x + y / 2)
      linarith
    linarith