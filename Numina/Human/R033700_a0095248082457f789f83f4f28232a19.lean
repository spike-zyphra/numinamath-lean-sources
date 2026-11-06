import Mathlib

/-Let $x$, $y$, and $z$ be distinct real numbers that sum to 0. Find the maximum possible value of $$\frac{xy+yz+zx}{x^2+y^2+z^2}.$$-/
theorem algebra_20368 :
    IsGreatest {m : ℝ | ∃x y z : ℝ, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x + y + z = 0 ∧ m = (x * y + y * z + z * x) / (x ^ 2 + y ^ 2 + z ^ 2)} (-1 / 2) := by
  simp [IsGreatest, upperBounds]
  refine ⟨?_, ?_⟩
  -- verify the upperBounds can be achieve
  . use 1
    use 2
    norm_num
    use (-3)
    norm_num
  -- prove the upperBounds
  . intro m x y hxy z _ _ hsum hm
    -- show that the dominator ≠ 0
    have ne0 : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 := by
      contrapose! hxy
      -- show that x = y = z = 0
      repeat rw [add_eq_zero_iff_of_nonneg] at hxy
      repeat rw [sq_eq_zero_iff] at hxy
      linarith only [hxy]

      all_goals positivity
    -- show that m = -1 / 2
    have equation₁ : m = -1 / 2 := by
      rw [hm]
      field_simp
      ring_nf 
      -- show that (x + y + z) ^ 2 = 0
      have pow : (x + y + z) ^ 2 = 0 := by rw [hsum]; norm_num

      linarith only [pow]
    linarith only [equation₁]
