import Mathlib

theorem algebra_103291 :
    IsLeast {t : ℝ | ∃ x y z, x + 2 * y + 3 * z = 1 ∧ t = x ^ 2 + y ^ 2 + z ^ 2} (1 / 14) := by 
  constructor
  · -- Show 1/14 is in the set
    use 1 / 14, 1 / 7, 3 / 14 
    constructor
    · -- Show 1/14 + 2*(1/7) + 3*(3/14) = 1
      norm_num
    · -- Show 1/14 = (1/14)^2 + (1/7)^2 + (3/14)^2
      norm_num
  · -- Show there is no smaller element in the set
    intro t ht
    rcases ht with ⟨x, y, z, h1, h2⟩
    have h3 : x ^ 2 + y ^ 2 + z ^ 2 ≥ 1 / 14 := by 
      nlinarith [sq_nonneg (x - 1 / 14), sq_nonneg (y - 1 / 7), sq_nonneg (z - 3 / 14),
        h1, sq_nonneg (x * 2 - y * 1), sq_nonneg (x * 3 - z * 1), sq_nonneg (y * 3 - z * 2)]
    have ht' : t = x ^ 2 + y ^ 2 + z ^ 2 := by linarith 
    linarith [ht', h3]