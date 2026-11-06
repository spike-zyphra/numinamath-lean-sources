import Mathlib

theorem algebra_21777 :
    IsLeast {x | ∃ a b c d : ℝ, a + b + c + d = 17 ∧ a * b + b * c + c * d + d * a = 46 ∧ x = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2} (197 / 2) := by
  constructor
  · -- Show that 197/2 is in the set, by constructing specific values
    use (17 + Real.sqrt 105) / 4, (17 - Real.sqrt 105) / 4, (17 + Real.sqrt 105) / 4, (17 - Real.sqrt 105) / 4 
    constructor
    · -- Check that a + b + c + d = 17
      ring_nf
    constructor
    · -- Check that a * b + b * c + c * d + d * a = 46
      nlinarith [Real.sqrt_nonneg 105, Real.sq_sqrt (show (0 : ℝ) ≤ (105 : ℝ) by norm_num)]
    · -- Check that x = a^2 + b^2 + c^2 + d^2
      nlinarith [Real.sqrt_nonneg 105, Real.sq_sqrt (show (0 : ℝ) ≤ (105 : ℝ) by norm_num)]
  · -- Show that 197/2 is minimal
    intro x hx
    rcases hx with ⟨a, b, c, d, h1, h2, h3⟩
    nlinarith [sq_nonneg (a + c - (b + d)), sq_nonneg (a - c + (b - d)), sq_nonneg (a - c - (b - d)), sq_nonneg (a + c - (b + d)), sq_nonneg ((a + c) - 17 / 2), sq_nonneg ((b + d) - 17 / 2)]