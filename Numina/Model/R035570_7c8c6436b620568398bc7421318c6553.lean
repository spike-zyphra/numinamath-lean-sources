import Mathlib

theorem algebra_21748 :
    IsGreatest {z : ℝ | ∃ x y, z = (x - y) / (x ^ 4 + y ^ 4 + 6)} (1 / 4) := by
  constructor
  · -- Show 1/4 is in the set
    use 1, -1
    norm_num
  · -- Show 1/4 is greatest in the set
    intro z h
    rcases h with ⟨x, y, hz⟩
    have h1 : (x - y) / (x ^ 4 + y ^ 4 + 6) ≤ 1 / 4 := by
      have h2 : x ^ 4 + y ^ 4 + 6 ≥ 4 * (x - y) := by
        nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (y + 1),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y), sq_nonneg (x + y),
          sq_nonneg (x^2 - y^2), sq_nonneg (x - 1), sq_nonneg (y + 1),
          sq_nonneg (x^2 + y^2 - 2), sq_nonneg (x^2 - y^2 - 0)]
      have h5 : x ^ 4 + y ^ 4 + 6 > 0 := by
        nlinarith [sq_nonneg (x^2), sq_nonneg (y^2), sq_nonneg (x - y), sq_nonneg (x + y)]
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    have h3 : z ≤ 1 / 4 := by
      linarith [hz, h1]
    linarith