import Mathlib

theorem algebra_4523 : IsLeast {z : ℝ | ∃ a b c : ℝ, z = a + b + c ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a * b * c = (2 + 10 / 27 : ℝ)} 4 := by
  constructor
  · -- First part: proving 4 is achievable
    use 4 / 3, 4 / 3, 4 / 3
    norm_num

  · -- Second part: proving no value less than 4 is achievable
    intro z h
    rcases h with ⟨a, b, c, hz, ha, hb, hc, hprod⟩

    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha, hprod]