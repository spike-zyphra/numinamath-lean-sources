import Mathlib

open Real BigOperators Finset

lemma lemma_1 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 1) : 4 ≤ 1 / a + 1 / b := by
  have h1 : 0 < a * b := by
    nlinarith
  have h2 : a * b ≤ 1 / 4 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 1), mul_pos ha hb]
  have h3 : 1 / a + 1 / b - 4 ≥ 0 := by
    have h4 : 1 / a + 1 / b - 4 = (1 - 4 * (a * b)) / (a * b) := by
      field_simp [ha.ne', hb.ne']
      nlinarith
    rw [h4]
    have h5 : 1 - 4 * (a * b) ≥ 0 := by
      nlinarith [h2]
    apply div_nonneg
    .
      linarith
    .
      nlinarith
  linarith

theorem algebra_15285 :
  IsLeast {x | ∃ a : Fin 12 → ℝ, (∀ i, 0 < a i) ∧ (∑ i, a i) = 1 ∧ x = ∑ i, 1 / a i} 144 := by
  constructor
  · -- Show 144 is in the set
    use (λ _ => (1 / 12 : ℝ))
    constructor
    · -- Show all the numbers are positive
      intro i
      norm_num
    constructor
    · -- Show the sum is 1
      simp [Finset.sum_const, Finset.card_univ]
      all_goals norm_num
    · -- Show 144 equals the sum of reciprocals
      simp [Finset.sum_const, Finset.card_univ]
      all_goals norm_num
  · -- Show 144 is the minimum
    intro x hx
    rcases hx with ⟨a, ha_pos, ha_sum, hx_eq⟩
    have h1 : ∑ i : Fin 12, (a i) = 1 := ha_sum
    have h2 : ∑ i : Fin 12, (1 / a i) ≥ 144 := by
      have h4 : (∑ i : Fin 12, (a i)) * (∑ i : Fin 12, (1 / a i)) ≥ (∑ i : Fin 12, (1 : ℝ)) ^ 2 := by
        have h9 : ∀ i : Fin 12, a i > 0 := by
          intro i
          exact ha_pos i
        have h99 : (∑ i : Fin 12, (a i)) * (∑ i : Fin 12, (1 / a i)) - (∑ i : Fin 12, (1 : ℝ)) ^ 2 ≥ 0 := by
          have h99 : (∑ i : Fin 12, (a i)) * (∑ i : Fin 12, (1 / a i)) ≥ (∑ i : Fin 12, (1 : ℝ)) ^ 2 := by
            have h99 : (∑ i : Fin 12, √(a i) * √(1 / a i)) = (∑ i : Fin 12, (1 : ℝ)) := by
              have h98 : ∀ i : Fin 12, √(a i) * √(1 / a i) = (1 : ℝ) := by
                intro i
                have h3 : 0 < a i := ha_pos i
                have h4 : √(a i) * √(1 / a i) = √(a i * (1 / a i)) := by
                  rw [Real.sqrt_mul (by linarith)]
                rw [h4]
                have h5 : a i * (1 / a i) = 1 := by
                  field_simp
                rw [h5]
                simp
              have h999 : (∑ i : Fin 12, √(a i) * √(1 / a i)) = (∑ i : Fin 12, (1 : ℝ)) := by
                apply Finset.sum_congr
                . rfl
                intro i hi
                specialize h98 i
                linarith [h98]
              linarith [h999]
            have h76 : (∑ i : Fin 12, (√(a i) ^ 2)) = (∑ i : Fin 12, (a i)) := by
              apply Finset.sum_congr
              . rfl
              intro i hi
              have h75 : √(a i) ^ 2 = a i := by
                apply Real.sq_sqrt
                linarith [ha_pos i]
              nlinarith [h75]
            have h77 : (∑ i : Fin 12, (√(1 / a i) ^ 2)) = (∑ i : Fin 12, (1 / a i)) := by
              apply Finset.sum_congr
              . rfl
              intro i hi
              have h78 : 0 < a i := ha_pos i
              have h79 : √(1 / a i) ^ 2 = 1 / a i := by
                apply Real.sq_sqrt
                positivity
              nlinarith [h79]
            have h78 : (∑ i : Fin 12, √(a i) * √(1 / a i)) ^ 2 ≤ (∑ i : Fin 12, (√(a i) ^ 2)) * (∑ i : Fin 12, (√(1 / a i) ^ 2)) := by
              apply Finset.sum_mul_sq_le_sq_mul_sq
            rw [h99, h76, h77] at h78
            nlinarith
          nlinarith
        linarith
      have h6 : (∑ i : Fin 12, (1 : ℝ)) = (12 : ℝ) := by
        simp [Finset.sum_const, Finset.card_univ]
        <;> norm_num
      have h88 : (∑ i : Fin 12, (a i)) = 1 := by
        linarith [h1]
      nlinarith [h4, h6, h88]
    linarith [hx_eq, h2]