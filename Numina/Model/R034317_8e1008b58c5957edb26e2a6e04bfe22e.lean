import Mathlib

theorem inequalities_598936 (a b c : ℝ) (ha : a ∈ Set.Icc (1 / 2) 1) (hb : b ∈ Set.Icc (1 / 2) 1) (hc : c ∈ Set.Icc (1 / 2) 1) :
    a / b + b / a ≤ 5 / 2 ∧ (a * b + b * c) / (a ^ 2 + 2 * b ^ 2 + c ^ 2) ≥ 2 / 5 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  constructor
  · -- Prove the first inequality: a / b + b / a ≤ 5 / 2
    have h1 : 0 < b := by linarith
    have h2 : 0 < a := by linarith
    have h3 : a / b + b / a - 5 / 2 ≤ 0 := by
      have h4 : a / b + b / a - 5 / 2 = (2 * a ^ 2 + 2 * b ^ 2 - 5 * a * b) / (2 * a * b) := by
        field_simp
        ring
      rw [h4]
      have h5 : 0 < (2 * a * b : ℝ) := by
        positivity
      have h6 : 2 * a ^ 2 + 2 * b ^ 2 - 5 * a * b ≤ 0 := by
        nlinarith [mul_self_nonneg (a - b), mul_self_nonneg (a - 1 / 2), mul_self_nonneg (b - 1 / 2), 
          mul_self_nonneg (a - 1), mul_self_nonneg (b - 1),
          mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1),
          mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1),
          mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2),
          mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hc2)]
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · nlinarith
    linarith
  · -- Prove the second inequality: (a * b + b * c) / (a ^ 2 + 2 * b ^ 2 + c ^ 2) ≥ 2 / 5
    have h7 : 0 < a ^ 2 + 2 * b ^ 2 + c ^ 2 := by
      nlinarith [ha1, ha2, hb1, hb2, hc1, hc2]
    have h8 : (a * b + b * c) / (a ^ 2 + 2 * b ^ 2 + c ^ 2) ≥ 2 / 5 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
        mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1), 
        mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hc1),
        mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1), 
        mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2),
        mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hc2), 
        mul_nonneg (sub_nonneg.mpr hb2) (sub_nonneg.mpr hc2)]
    linarith