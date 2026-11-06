import Mathlib

theorem algebra_207392 :
    IsGreatest {d | ∃ a b c : ℝ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a * b * c + 2 * a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + c * a - c * b - 4 * a + 4 * b - c = 28 ∧ d = a + b + c} 6 := by
  constructor
  · -- Show $6$ is in the set.
    use 3, 1, 2
    norm_num
  · -- Show no value greater than $6$ is in the set.
    intro d hd
    rcases hd with ⟨a, b, c, ha, hb, hc, heq, hd⟩
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 1), sq_nonneg (c - 2),
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb),
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hc),
      mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]