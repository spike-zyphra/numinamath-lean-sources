import Mathlib

open Real Set

/- Let $0<{}x<{}1, a$ and $b$ be constants greater than zero, then the minimum value of $\frac{{{a}^{2}}}{x}+\frac{{{b}^{2}}}{1-x}$ is ___          ___. -/
theorem algebra_10823 (x : ℝ) (hx : 0 < x ∧ x < 1) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IsLeast {y | ∃ x : ℝ, 0 < x ∧ x < 1 ∧ y = a ^ 2 / x + b ^ 2 / (1 - x)} ((a + b) ^ 2) := by
  constructor
  · -- Show that (a + b)^2 is in the set
    use a / (a + b)
    constructor
    · -- Show 0 < a / (a + b)
      have h1 : 0 < a := ha
      have h2 : 0 < b := hb
      have h3 : 0 < a + b := by linarith
      apply div_pos
      all_goals linarith
    constructor
    · -- Show a / (a + b) < 1
      have h1 : 0 < a := ha
      have h2 : 0 < b := hb
      have h3 : 0 < a + b := by linarith
      have h4 : a < a + b := by linarith
      apply (div_lt_one (by linarith)).mpr
      linarith
    · -- Show that (a + b)^2 = a^2 / x + b^2 / (1 - x)
      have h1 : 0 < a := ha
      have h2 : 0 < b := hb
      have h3 : 0 < a + b := by linarith
      field_simp
      <;> ring_nf <;> field_simp <;> ring
  · -- Show that (a + b)^2 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx1, hx2, heq⟩
    have h3 : a ^ 2 / x + b ^ 2 / (1 - x) ≥ (a + b) ^ 2 := by
      have h4 : 0 < x := hx1
      have h5 : 0 < 1 - x := by linarith
      have h6 : a ^ 2 / x + b ^ 2 / (1 - x) - (a + b) ^ 2 ≥ 0 := by
        have h7 : 0 < x * (1 - x) := by
          positivity
        have h8 : a ^ 2 / x + b ^ 2 / (1 - x) - (a + b) ^ 2 = (a ^ 2 * (1 - x) + b ^ 2 * x - (a + b) ^ 2 * (x * (1 - x))) / (x * (1 - x)) := by
          field_simp
          <;> ring
        rw [h8] at *
        have h9 : a ^ 2 * (1 - x) + b ^ 2 * x - (a + b) ^ 2 * (x * (1 - x)) ≥ 0 := by
          nlinarith [sq_nonneg (a * (1 - x) - b * x), sq_nonneg (a - b), sq_nonneg (x - a / (a + b)), sq_nonneg ((1 - x) - b / (a + b)), mul_pos ha hb, mul_pos ha (show 0 < 1 - x by linarith), mul_pos hb (show 0 < 1 - x by linarith), mul_pos (show 0 < x by linarith) (show 0 < 1 - x by linarith), sq_nonneg (a * x - b * (1 - x))]
        apply div_nonneg
        · -- Show numerator is non-negative
          linarith
        · -- Show denominator is non-negative
          positivity
      linarith
    linarith [heq, h3]