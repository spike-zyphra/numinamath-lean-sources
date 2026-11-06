import Mathlib

open Real

namespace inequalities_95940

variable {s : Set ℝ} {f : ℝ → ℝ}

theorem ConvexOn.map_sum_le_fin_three_real {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hf : ConvexOn ℝ s f)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s)
    (hw : w₁ + w₂ + w₃ = 1) :
    f (w₁ • p₁ + w₂ • p₂ + w₃ • p₃) ≤ w₁ • f p₁ + w₂ • f p₂ + w₃ • f p₃ := by
  have h₀ : (∀ i ∈ Finset.univ, 0 ≤ ![w₁, w₂, w₃] i) := by
    intro i
    fin_cases i
    all_goals simpa
  have h₁ : (∑ i ∈ Finset.univ, ![w₁, w₂, w₃] i = 1) := by
    simp [Fin.sum_univ_three, hw]
  have hmem : (∀ i ∈ Finset.univ, ![p₁, p₂, p₃] i ∈ s) := by
    intro i
    fin_cases i
    all_goals simpa
  convert (ConvexOn.map_sum_le hf h₀ h₁ hmem)
  all_goals simp [Fin.sum_univ_three]

theorem ConvexOn.map_sum_le_fin_three_real' {p₁ p₂ p₃ : ℝ} (hf : ConvexOn ℝ s f)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) :
    f (((1 : ℝ) / 3) • p₁ + ((1 : ℝ) / 3) • p₂ + ((1 : ℝ) / 3) • p₃) ≤
    ((1 : ℝ) / 3) • f p₁ + ((1 : ℝ) / 3) • f p₂ + ((1 : ℝ) / 3) • f p₃ := by
  refine @ConvexOn.map_sum_le_fin_three_real _ _ ((1 : ℝ) / 3) ((1 : ℝ) / 3) ((1 : ℝ) / 3) _ _ _ hf ?_ ?_ ?_ hp₁ hp₂ hp₃ ?_
  all_goals norm_num

end inequalities_95940

open inequalities_95940

theorem inequalities_95940 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ a * b ^ b * c ^ c ≥ (a * b * c) ^ ((a + b + c) / 3) := by

  have h1 : a ^ a * b ^ b * c ^ c ≥ (a * b * c) ^ ((a + b + c) / 3) := by
    have h5 : Real.log (a ^ a * b ^ b * c ^ c) ≥ Real.log ((a * b * c) ^ ((a + b + c) / 3)) := by
      have h14 : Real.log (a ^ a * b ^ b * c ^ c) = a * (Real.log a) + b * (Real.log b) + c * (Real.log c) := by
        have h8 : Real.log (a ^ a * b ^ b * c ^ c) = Real.log (a ^ a) + Real.log (b ^ b) + Real.log (c ^ c) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
        have h10 : Real.log (a ^ a) = a * Real.log a := by 
          rw [Real.log_rpow]
          all_goals
            positivity
        have h11 : Real.log (b ^ b) = b * Real.log b := by 
          rw [Real.log_rpow]
          all_goals
            positivity
        have h12 : Real.log (c ^ c) = c * Real.log c := by 
          rw [Real.log_rpow]
          all_goals
            positivity
        linarith
      have h13 : Real.log ((a * b * c) ^ ((a + b + c) / 3)) = ((a + b + c) / 3) * (Real.log a + Real.log b + Real.log c) := by
        have h7 : Real.log ((a * b * c) ^ ((a + b + c) / 3)) = ((a + b + c) / 3) * Real.log (a * b * c) := by 
          rw [Real.log_rpow]
          all_goals 
            positivity
        have h8 : Real.log (a * b * c) = Real.log a + Real.log b + Real.log c := by
          simp [Real.log_mul, ha.ne.symm, hb.ne.symm, hc.ne.symm]
        rw [h7, h8]
      rw [h14, h13]
      have h9 : a * (Real.log a) + b * (Real.log b) + c * (Real.log c) ≥ ((a + b + c) / 3) * (Real.log a + Real.log b + Real.log c) := by
        have h17 : (a - b) * (Real.log a - Real.log b) ≥ 0 := by
          by_cases h : a ≥ b
          · -- Assume a ≥ b
            have h10 : Real.log a ≥ Real.log b := by
              apply Real.log_le_log
              all_goals
              linarith
            nlinarith
          · -- Assume b > a
            have h12 : Real.log b > Real.log a := by
              apply Real.log_lt_log
              all_goals
              linarith
            have h11 : Real.log a < Real.log b := by linarith
            nlinarith
        have h18 : (b - c) * (Real.log b - Real.log c) ≥ 0 := by
          by_cases h : b ≥ c
          · -- Assume b ≥ c
            have h13 : Real.log b ≥ Real.log c := by
              apply Real.log_le_log
              all_goals
              linarith
            nlinarith
          · -- Assume c > b
            have h14 : Real.log c > Real.log b := by
              apply Real.log_lt_log
              all_goals
              linarith
            have h15 : Real.log b < Real.log c := by linarith
            nlinarith
        have h19 : (c - a) * (Real.log c - Real.log a) ≥ 0 := by
          by_cases h : c ≥ a
          · -- Assume c ≥ a
            have h16 : Real.log c ≥ Real.log a := by
              apply Real.log_le_log
              all_goals
              linarith
            nlinarith
          · -- Assume a > c
            have h17 : Real.log a > Real.log c := by
              apply Real.log_lt_log
              all_goals
              linarith
            have h18 : Real.log c < Real.log a := by linarith
            nlinarith
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (Real.log a - Real.log b), sq_nonneg (Real.log b - Real.log c), sq_nonneg (Real.log c - Real.log a),
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
          mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith),
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a by linarith)]
      linarith
    have h4 : a ^ a * b ^ b * c ^ c ≥ (a * b * c) ^ ((a + b + c) / 3) := by
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp at h5
      linarith
    linarith
  linarith