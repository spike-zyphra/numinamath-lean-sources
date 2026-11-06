import Mathlib

theorem inequalities_150644 (n : ℕ) :
    IsLeast {x | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 2 ∧ x = 1 / (1 + a ^ n) + 1 / (1 + b ^ n)} 1
  := by
  constructor
  · -- First part: prove 1 is in the set.
    use 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    all_goals norm_num
  · -- Second part: prove it's minimal
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h1, hx⟩
    have h4 : (a ^ n) * (b ^ n) ≤ 1 := by
      have h5 : (a ^ n) * (b ^ n) = (a * b) ^ n := by
        rw [mul_pow]
      rw [h5]
      have h3 : a * b ≤ 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a + b - 2)]
      have h6 : (a * b) ^ n ≤ (1 : ℝ) ^ n := by
        apply pow_le_pow_left
        all_goals
          nlinarith [show 0 ≤ a * b by positivity]
      have h7 : (1 : ℝ) ^ n = 1 := by
        have : ∀ (n : ℕ), (1 : ℝ) ^ n = 1 := by
          intro n
          exact one_pow n
        specialize this n
        simpa using this
      nlinarith
    have h5 : 1 / (1 + a ^ n) + 1 / (1 + b ^ n) ≥ 1 := by
      have h6 : 0 < (1 + a ^ n) := by
        have h7 : a ^ n > 0 := by positivity
        linarith
      have h7 : 0 < (1 + b ^ n) := by
        have h8 : b ^ n > 0 := by positivity
        linarith
      have h8 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) ) - 1 ≥ 0 := by
        have h9 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) ) - 1 = ( (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) ) / ( (1 + a ^ n) * (1 + b ^ n) ) := by
          field_simp
          <;> ring
        rw [h9] at *
        have h10 : (1 + a ^ n) * (1 + b ^ n) > 0 := mul_pos (by linarith) (by linarith)
        have h11 : ( (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) ) ≥ 0 := by
          have h12 : (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) = 1 - (a ^ n * b ^ n) := by
            ring_nf
          rw [h12]
          nlinarith [show a ^ n * b ^ n ≤ 1 by nlinarith [h4]]
        apply div_nonneg
        linarith
        linarith
      linarith
    linarith [show 1 / (1 + a ^ n) + 1 / (1 + b ^ n) ≥ 1 by linarith [h5]]