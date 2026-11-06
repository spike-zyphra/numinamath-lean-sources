import Mathlib

/- 4. (7 points) The numbers $a, b, c, d$ belong to the interval $[-7 ; 7]$. Find the maximum value of the expression $a+2 b+c+2 d-a b-b c-c d-d a$. -/
theorem algebra_195320 :
    IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
      a ∈ Set.Icc (-7) 7 ∧ b ∈ Set.Icc (-7) 7 ∧ c ∈ Set.Icc (-7) 7 ∧ d ∈ Set.Icc (-7) 7} 210 := by
  simp only [IsGreatest, Set.mem_Icc, Set.mem_setOf_eq, upperBounds, forall_exists_index, and_imp]
  constructor
  -- show that a = c = -7, b = d = 7 imply that the expression is equal to 210
  · use -7, 7, -7, 7
    norm_num
  -- assume that s = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a for a, b, c, d ∈ [-7, 7]
  -- and show that s ≤ 210
  · intro s a b c d hs ha1 ha2 hb1 hb2 hc1 hc2 hd1 hd2
    -- the problem can be solved instantly with nlinarith
    --nlinarith
    set x := a + c
    set y := b + d
    -- let x = a + c and y = b + d
    -- it follows that s = (y - 1) * (2 - x) + 2
    have eq : s = (y - 1) * (2 - x) + 2 := by linear_combination hs
    -- it is easy to derive bounds of x and y
    have hy : y - 1 ≤ 13 ∧ -15 ≤ y - 1 := by dsimp [y]; constructor <;> linarith
    have hx : 2 - x ≤ 16 ∧ -12 ≤ 2 - x := by dsimp [x]; constructor <;> linarith
    -- consider 4 cases for different signs of (y - 1) and (2 - x)
    -- and show that (y - 1) * (2 - x) + 2 ≤ 210 in all cases
    by_cases h1 : y - 1 ≤ 0 <;> by_cases h2 : 2 - x ≤ 0
    · have : (y - 1) * (2 - x) ≤ -15 * -12 := mul_le_mul_of_nonpos_of_nonpos hy.2 hx.2 (by norm_num) h2
      linarith
    · have : (y - 1) * (2 - x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 (by linarith)
      linarith
    · have : (y - 1) * (2 - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h2
      linarith
    · have : (y - 1) * (2 - x) ≤ 13 * 16 := mul_le_mul_of_nonneg hy.1 hx.1 (by linarith) (by linarith)
      linarith