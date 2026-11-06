import Mathlib

open Real

lemma lemma_1 (x : Fin 4 → ℝ) (y : Fin 4 → ℝ)
    (hy : ∀ i, 0 < y i) :
    ∑ i, (x i)^2 / y i ≥ ((∑ i, x i)^2) / (∑ i, y i) := by
  have h1 : ∀ i : Fin 4, 0 < y i := hy
  have h2 : ∑ i : Fin 4, y i > 0 := by
    have h10 : 0 < y 0 := h1 0
    have h11 : 0 < y 1 := h1 1
    have h12 : 0 < y 2 := h1 2
    have h13 : 0 < y 3 := h1 3
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
    positivity
  apply Finset.sq_sum_div_le_sum_sq_div
  intro i hi
  apply h1 i


theorem inequalities_319 (x : Fin 4 → ℝ) (hx : ∀ i, 0 < x i) :
    1 ≤ x 0 / (3 * x 1 + x 2) + x 1 / (3 * x 2 + x 3) +
        x 2 / (3 * x 3 + x 0) + x 3 / (3 * x 0 + x 1) := by
  have h0 : 0 < x 0 := hx 0
  have h1 : 0 < x 1 := hx 1
  have h2 : 0 < x 2 := hx 2
  have h3 : 0 < x 3 := hx 3
  have h4 : x 0 / (3 * x 1 + x 2) + x 1 / (3 * x 2 + x 3) + x 2 / (3 * x 3 + x 0) + x 3 / (3 * x 0 + x 1) ≥ 1 := by
    -- we rewrite the expression by multiplying denominators
    have h5 : x 0 / (3 * x 1 + x 2) + x 1 / (3 * x 2 + x 3) + x 2 / (3 * x 3 + x 0) + x 3 / (3 * x 0 + x 1) =
        (x 0 ^ 2 / (x 0 * (3 * x 1 + x 2)) + x 1 ^ 2 / (x 1 * (3 * x 2 + x 3)) + x 2 ^ 2 / (x 2 * (3 * x 3 + x 0)) + x 3 ^ 2 / (x 3 * (3 * x 0 + x 1))) := by
      have h7 : x 0 ≠ 0 := by linarith
      have h8 : x 1 ≠ 0 := by linarith
      have h9 : x 2 ≠ 0 := by linarith
      have h10 : x 3 ≠ 0 := by linarith
      field_simp
      <;> ring
    rw [h5]
    -- Now apply Cauchy-Schwarz with weights.
    have h6 : x 0 ^ 2 / (x 0 * (3 * x 1 + x 2)) + x 1 ^ 2 / (x 1 * (3 * x 2 + x 3)) + x 2 ^ 2 / (x 2 * (3 * x 3 + x 0)) + x 3 ^ 2 / (x 3 * (3 * x 0 + x 1)) ≥
        ((x 0 + x 1 + x 2 + x 3) ^ 2) / (x 0 * (3 * x 1 + x 2) + x 1 * (3 * x 2 + x 3) + x 2 * (3 * x 3 + x 0) + x 3 * (3 * x 0 + x 1)) := by
      let x2 : Fin 4 → ℝ := fun i => match i with
        | 0 => x 0
        | 1 => x 1
        | 2 => x 2
        | 3 => x 3
        | _ => 0
      let y2 : Fin 4 → ℝ := fun i => match i with
        | 0 => x 0 * (3 * x 1 + x 2)
        | 1 => x 1 * (3 * x 2 + x 3)
        | 2 => x 2 * (3 * x 3 + x 0)
        | 3 => x 3 * (3 * x 0 + x 1)
        | _ => 0
      have hy2 : ∀ i, 0 < y2 i := by
        intro i
        fin_cases i <;> simp [y2] <;> positivity
      have h110 : ∑ i : Fin 4, (x2 i) ^ 2 / y2 i ≥ ((∑ i : Fin 4, x2 i) ^ 2) / (∑ i : Fin 4, y2 i) := by
        apply lemma_1 x2 y2 hy2
      have h170 : ∑ i : Fin 4, (x2 i) ^ 2 / y2 i = x 0 ^ 2 / (x 0 * (3 * x 1 + x 2)) + x 1 ^ 2 / (x 1 * (3 * x 2 + x 3)) + x 2 ^ 2 / (x 2 * (3 * x 3 + x 0)) + x 3 ^ 2 / (x 3 * (3 * x 0 + x 1)) := by
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, x2, y2]
      have h171 : ((∑ i : Fin 4, x2 i) ^ 2) / (∑ i : Fin 4, y2 i) = ((x 0 + x 1 + x 2 + x 3) ^ 2) / (x 0 * (3 * x 1 + x 2) + x 1 * (3 * x 2 + x 3) + x 2 * (3 * x 3 + x 0) + x 3 * (3 * x 0 + x 1)) := by
        simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, x2, y2]
      rw [h170, h171] at h110
      linarith
    -- Multiply denominators to get $\frac{(\sum x_i)^2}{\sum \text{denominator terms}} \ge 1$.
    have h8 : ((x 0 + x 1 + x 2 + x 3) ^ 2) / (x 0 * (3 * x 1 + x 2) + x 1 * (3 * x 2 + x 3) + x 2 * (3 * x 3 + x 0) + x 3 * (3 * x 0 + x 1)) ≥ 1 := by
      have h9 : x 0 * (3 * x 1 + x 2) + x 1 * (3 * x 2 + x 3) + x 2 * (3 * x 3 + x 0) + x 3 * (3 * x 0 + x 1) > 0 := by
        positivity
      have h10 : (x 0 + x 1 + x 2 + x 3) ^ 2 ≥ x 0 * (3 * x 1 + x 2) + x 1 * (3 * x 2 + x 3) + x 2 * (3 * x 3 + x 0) + x 3 * (3 * x 0 + x 1) := by
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 0 - x 3), sq_nonneg (x 1 - x 2), sq_nonneg (x 1 - x 3), sq_nonneg (x 2 - x 3),
          mul_pos h0 h1, mul_pos h0 h2, mul_pos h0 h3, mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3]
      have h11 : ((x 0 + x 1 + x 2 + x 3) ^ 2) / (x 0 * (3 * x 1 + x 2) + x 1 * (3 * x 2 + x 3) + x 2 * (3 * x 3 + x 0) + x 3 * (3 * x 0 + x 1)) ≥ 1 := by
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith
      linarith
    linarith
  linarith