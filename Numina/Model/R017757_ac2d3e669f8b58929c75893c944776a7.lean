import Mathlib

theorem algebra_115755 (b : ℕ) :
    (∃ x : ℝ, x^2 + b * x + 25 = 0) ↔ b ≥ 10 := by
  constructor
  · -- Assume there exists a real root, prove b ≥ 10
    intro h
    rcases h with ⟨x, hx⟩
    have h1 : (b : ℝ) ≥ (0 : ℝ) := by positivity
    have h2 : x ^ 2 + (b : ℝ) * x + (25 : ℝ) = 0 := by simpa using hx
    have h3 : (2 * x + (b : ℝ)) ^ 2 = (b : ℝ) ^ 2 - (100 : ℝ) := by
      nlinarith [h2]
    have h4 : (b : ℝ) ^ 2 - (100 : ℝ) ≥ 0 := by
      nlinarith [sq_nonneg (2 * x + (b : ℝ)), h3]
    have h5 : (b : ℝ) ≥ (10 : ℝ) := by nlinarith [h4, sq_nonneg ((b : ℝ) : ℝ), h1]
    have hb : b ≥ 10 := by
      by_contra h
      push_neg at h
      have h6 : b < 10 := by omega
      have h7 : b ≤ 9 := by omega
      have h8 : (b : ℝ) ≤ (9 : ℝ) := by exact_mod_cast h7
      nlinarith [h5, h8]
    exact_mod_cast hb
  · -- Assume b ≥ 10 prove ∃ x : ℝ, x^2 + b * x + 25 = 0
    intro h
    have hb10 : b ≥ 10 := by linarith
    have h2 : (b : ℝ) ≥ (10 : ℝ) := by
      exact_mod_cast hb10
    have h3 : (b : ℝ) ^ 2 ≥ (100 : ℝ) := by nlinarith [h2]
    use (- (b : ℝ) - Real.sqrt ((b : ℝ) ^ 2 - (100 : ℝ)) ) / (2 : ℝ)
    nlinarith [ Real.sqrt_nonneg ((b : ℝ) ^ 2 - (100 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (b : ℝ) ^ 2 - (100 : ℝ) by nlinarith [h3] ) ]