import Mathlib

open Real
open scoped BigOperators

theorem inequalities_37616 (a b c s : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a ≥ b ∧ b ≥ c)
  (h₂ : s ≥ (a + 1))
  (h₃ : s = (a + b + c) / 2) :
  (s - c) / sqrt a + (s - b) / sqrt c + (s - a) / sqrt b ≥
  (s - b) / sqrt a + (s - c) / sqrt b + (s - a) / sqrt c := by
  rcases h₀ with ⟨ha, hb, hc⟩
  have h4 : 0 < a := by linarith
  have h5 : 0 < b := by linarith
  have h6 : 0 < c := by linarith
  have h7 : b + c ≥ a + 2 := by
    nlinarith [h₂, h₃]
  have h8 : 0 < sqrt a := by positivity
  have h9 : 0 < sqrt b := by positivity
  have h10 : 0 < sqrt c := by positivity
  have h11 : sqrt a ≥ sqrt b := by
    apply Real.sqrt_le_sqrt
    linarith [h₁.1]
  have h12 : sqrt b ≥ sqrt c := by
    apply Real.sqrt_le_sqrt
    linarith [h₁.2]
  have h13 : (b - c) * (sqrt b * sqrt c) + (a - b) * (sqrt a * sqrt b) + (c - a) * (sqrt a * sqrt c) ≥ 0 := by
    nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt b - sqrt c), sq_nonneg (sqrt a - sqrt c),
      Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
      mul_nonneg (show 0 ≤ sqrt a - sqrt b by nlinarith [h11]) (show 0 ≤ sqrt b - sqrt c by nlinarith [h12]),
      mul_nonneg (show 0 ≤ sqrt b - sqrt c by nlinarith [h12]) (show 0 ≤ sqrt a by positivity),
      mul_nonneg (show 0 ≤ sqrt a - sqrt b by nlinarith [h11]) (show 0 ≤ sqrt c by positivity),
      Real.sq_sqrt (show (0 : ℝ) ≤ a by positivity),
      Real.sq_sqrt (show (0 : ℝ) ≤ b by positivity),
      Real.sq_sqrt (show (0 : ℝ) ≤ c by positivity),
      h7]
  have h14 : (s - c) / sqrt a + (s - b) / sqrt c + (s - a) / sqrt b - ((s - b) / sqrt a + (s - c) / sqrt b + (s - a) / sqrt c) ≥ 0 := by
    have h15 : (s - c) / sqrt a + (s - b) / sqrt c + (s - a) / sqrt b - ((s - b) / sqrt a + (s - c) / sqrt b + (s - a) / sqrt c) =
        ((b - c) * (sqrt b * sqrt c) + (a - b) * (sqrt a * sqrt b) + (c - a) * (sqrt a * sqrt c)) / (sqrt a * sqrt b * sqrt c) := by
      field_simp [hb.ne', ha.ne', hc.ne']
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ a by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ b by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ c by positivity)]
    rw [h15]
    apply div_nonneg
    linarith [h13]
    positivity
  linarith