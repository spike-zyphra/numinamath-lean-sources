import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_113111 :
  IsLeast {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 + c^2 = 1 ∧ x = a/(1-a^2) + b/(1-b^2) + c/(1-c^2)} (3*sqrt 3 / 2) := by
  constructor
  · -- First, show 3*sqrt(3)/2 is in the set.
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3
    constructor
    · -- Show a > 0
      positivity
    constructor
    · -- Show b > 0
      positivity
    constructor
    · -- Show c > 0
      positivity
    constructor
    · -- Show a^2 + b^2 + c^2 = 1
      have h1 : (Real.sqrt 3 / 3 : ℝ) ^ 2 = (1 / 3 : ℝ) := by
        calc
          (Real.sqrt 3 / 3 : ℝ) ^ 2 = (Real.sqrt 3 ^ 2) / 9 := by ring_nf
          _ = 3 / 9 := by rw [Real.sq_sqrt]; all_goals norm_num
          _ = 1 / 3 := by norm_num
      nlinarith [h1]
    · -- Show x = a/(1-a^2) + b/(1-b^2) + c/(1-c^2)
      have h1 : (Real.sqrt 3 / 3 : ℝ) ^ 2 = (1 / 3 : ℝ) := by
        calc
          (Real.sqrt 3 / 3 : ℝ) ^ 2 = (Real.sqrt 3 ^ 2) / 9 := by ring_nf
          _ = 3 / 9 := by rw [Real.sq_sqrt]; all_goals norm_num
          _ = 1 / 3 := by norm_num
      have h2 : (Real.sqrt 3 / 3 : ℝ) / (1 - (Real.sqrt 3 / 3 : ℝ) ^ 2) = Real.sqrt 3 / 2 := by
        rw [h1]
        field_simp
        <;> ring_nf <;> field_simp
        <;> nlinarith [Real.sqrt_nonneg 3]
      linarith [h2]
  · -- Now, show 3*sqrt(3)/2 is minimal.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : a / (1 - a^2) + b / (1 - b^2) + c / (1 - c^2) ≥ 3 * Real.sqrt 3 / 2 := by
      have h3 : ∀ t : ℝ, t > 0 → t^2 < 1 → t / (1 - t^2) ≥ (3 * Real.sqrt 3 / 2) * t ^ 2 := by
        intro t ht ht2
        have ht0 : 1 - t^2 > 0 := by nlinarith
        have h4 : 0 < t := by linarith
        have h5 : 0 < 1 - t^2 := by nlinarith
        have h7 : t / (1 - t^2) - (3 * Real.sqrt 3 / 2) * t ^ 2 ≥ 0 := by
          have h8 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
          have h9 : Real.sqrt 3 > 0 := by positivity
          have h10 : t / (1 - t^2) - (3 * Real.sqrt 3 / 2) * t ^ 2 =
              (t - (3 * Real.sqrt 3 / 2) * t ^ 2 * (1 - t^2)) / (1 - t^2) := by
            field_simp [(show (1 - t^2 : ℝ) ≠ 0 by nlinarith)]
            <;> ring
          rw [h10]
          apply div_nonneg
          nlinarith [sq_nonneg (t ^ 2 - 1 / 3), sq_nonneg (t - Real.sqrt 3 / 3), sq_nonneg (t * (t - Real.sqrt 3 / 3)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (t ^ 2), mul_pos ht ht]
          all_goals positivity
        nlinarith
      have ha2 : a ^ 2 < 1 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
      have hb2 : b ^ 2 < 1 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
      have hc2 : c ^ 2 < 1 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
      have h4 : a / (1 - a^2) ≥ (3 * Real.sqrt 3 / 2) * a ^ 2 := by
        specialize h3 a ha ha2
        linarith
      have h5 : b / (1 - b^2) ≥ (3 * Real.sqrt 3 / 2) * b ^ 2 := by
        specialize h3 b hb hb2
        linarith
      have h6 : c / (1 - c^2) ≥ (3 * Real.sqrt 3 / 2) * c ^ 2 := by
        specialize h3 c hc hc2
        linarith
      have h7 : a / (1 - a^2) + b / (1 - b^2) + c / (1 - c^2) ≥ (3 * Real.sqrt 3 / 2) * (a^2 + b^2 + c^2) := by
        linarith [h4, h5, h6]
      have h8 : (3 * Real.sqrt 3 / 2) * (a^2 + b^2 + c^2) = (3 * Real.sqrt 3 / 2) := by
        rw [h1]
        <;> nlinarith
      nlinarith [h7, h8, h4, h5, h6]
    linarith [hx, h2]