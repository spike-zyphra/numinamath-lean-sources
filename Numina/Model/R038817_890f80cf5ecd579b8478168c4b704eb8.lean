import Mathlib

theorem algebra_20464 : IsLeast {z | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    z = (a + b + c) * ((a + b)^2 + (a + b + 4 * c)^2) / (a * b * c)} 100 := by
  constructor
  · -- Show 100 is in the set.
    use 2, 2, 1
    norm_num
  · -- Show 100 is the smallest.
    intro z h
    rcases h with ⟨a, b, c, ha, hb, hc, hz⟩
    have h1 : (a + b + c) * ((a + b)^2 + (a + b + 4 * c)^2) ≥ 100 * (a * b * c) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 2 * c), sq_nonneg (b - 2 * c),
        sq_nonneg (a * b - 2 * a * c), sq_nonneg (a * b - 2 * b * c), sq_nonneg (a * c - b * c),
          sq_nonneg (a + b - 4 * c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h2 : (a + b + c) * ((a + b)^2 + (a + b + 4 * c)^2) / (a * b * c) ≥ 100 := by
      have h3 : (a * b * c) > 0 := mul_pos (mul_pos ha hb) hc
      have h4 : (a + b + c) * ((a + b)^2 + (a + b + 4 * c)^2) ≥ 100 * (a * b * c) := by linarith [h1]
      have h5 : (a + b + c) * ((a + b)^2 + (a + b + 4 * c)^2) / (a * b * c) ≥ 100 := by
        apply (le_div_iff₀ (by positivity)).mpr
        linarith
      linarith
    linarith [hz, h2]