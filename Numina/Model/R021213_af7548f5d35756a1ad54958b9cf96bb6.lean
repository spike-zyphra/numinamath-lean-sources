import Mathlib

open Real

theorem algebra_172899 (k : ℕ) (hk : 0 < k) :
    (1 / k) * sqrt (1 - (1 / (k + 1))^2) -
    sqrt (1 - (1 / k)^2) * (1 / (k + 1)) =
    sqrt ((k + 1)^2 - 1) / (k * (k + 1)) -
    sqrt (k^2 - 1) / (k * (k + 1)) := by
  have hk1 : (k : ℝ) > 0 := by
    exact_mod_cast hk
  have hk2 : (k + 1 : ℝ) > 0 := by
    positivity
  have eq1 : (1 / (k : ℝ)) * sqrt (1 - (1 / (k + 1) : ℝ)^2) =
      sqrt ((k + 1)^2 - 1) / ((k : ℝ) * (k + 1 : ℝ)) := by
    have h1 : (1 - (1 / (k + 1) : ℝ)^2) = (((k + 1) : ℝ)^2 - 1) / ((k + 1 : ℝ)^2) := by
      field_simp at *
      <;> ring
    have h2 : sqrt (1 - (1 / (k + 1) : ℝ)^2) = sqrt (((k + 1) : ℝ)^2 - 1) / ((k + 1 : ℝ)) := by
      rw [h1]
      have h3 : sqrt (((k + 1 : ℝ)^2 - 1) / ((k + 1 : ℝ)^2)) =
          sqrt ((k + 1 : ℝ)^2 - 1) / sqrt ((k + 1 : ℝ)^2) := by
        rw [Real.sqrt_div (by
          have h6 : ((k + 1 : ℝ)^2 - 1) ≥ 0 := by
            nlinarith [sq_nonneg ((k : ℝ)), sq_nonneg ((k + 1 : ℝ))]
          nlinarith [Real.sqrt_nonneg ((k + 1 : ℝ)^2 - 1), Real.sqrt_nonneg ((k + 1 : ℝ)^2)]
        )
        ]
        all_goals positivity
      rw [h3]
      have h4 : sqrt ((k + 1 : ℝ)^2) = (k + 1 : ℝ) := by
        rw [Real.sqrt_sq (show 0 ≤ (k + 1 : ℝ) by positivity)]
      rw [h4]
      <;> field_simp <;> nlinarith [Real.sqrt_nonneg ((k + 1 : ℝ)^2 - 1), Real.sqrt_nonneg ((k + 1 : ℝ)^2)]
    rw [h2]
    field_simp
    <;> ring_nf <;> field_simp
    <;> nlinarith [Real.sqrt_nonneg ((k + 1 : ℝ)^2 - 1), Real.sqrt_nonneg ((k + 1 : ℝ)^2)]
  have eq2 : sqrt (1 - (1 / (k : ℝ))^2) * (1 / (k + 1 : ℝ)) =
      sqrt (k^2 - 1) / ((k : ℝ) * (k + 1 : ℝ)) := by
    have h2 : sqrt (1 - (1 / (k : ℝ))^2) = sqrt (k ^ 2 - 1) / (k : ℝ) := by
      have h4 : (1 - (1 / (k : ℝ))^2 : ℝ) = ((k : ℝ) ^ 2 - 1) / ((k : ℝ) ^ 2) := by
        field_simp
        <;> nlinarith
      rw [h4]
      have h5 : sqrt (((k : ℝ)^2 - 1) / (k : ℝ)^2) = sqrt ((k : ℝ)^2 - 1) / sqrt ((k : ℝ)^2) := by
        rw [Real.sqrt_div (by
          have h6 : (k : ℝ) ≥ 1 := by
            have h7 : (k : ℝ) ≥ (1 : ℝ) := by
              have h8 : (k : ℝ) ≥ (1 : ℝ) := by
                have h9 : k ≥ 1 := by linarith
                have h10 : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h9
                linarith
              linarith
            linarith
          nlinarith [h6]
        )
        ]
        all_goals positivity
      rw [h5]
      have h3 : sqrt ((k : ℝ) ^ 2) = (k : ℝ) := by
        rw [Real.sqrt_sq (show (0 : ℝ) ≤ (k : ℝ) by positivity)]
      rw [h3]
      <;> field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
      all_goals ring_nf <;> field_simp
      <;> ring_nf <;> field_simp
      all_goals ring_nf <;> field_simp
    rw [h2]
    <;> field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
    all_goals ring_nf <;> field_simp
    <;> ring_nf <;> field_simp
    all_goals ring_nf <;> field_simp
  rw [eq1, eq2]
  <;> field_simp
  <;> ring_nf
  <;> field_simp
  <;> ring_nf
  <;> norm_num
  <;> ring_nf <;> norm_num
  all_goals ring_nf <;> field_simp
  <;> ring_nf <;> norm_num