import Mathlib

open Real

/-- Auxiliary lemma : `sin A + sin B * sin C = √5 / 2 * sin (arccos (2 / √5) + A) + 1 / 2 * cos (B - C)`. -/
lemma p98' {A B C : ℝ}
            (hsum : A + B + C = π)
            : sin A + sin B * sin C = √5 / 2 * sin (arccos (2 / √5) + A) + 1 / 2 * cos (B - C) := by
  have h₁ : sin B * sin C = 1 / 2 * (cos (B - C) + cos A) := by
    calc
      sin B * sin C = 1 / 2 * (cos (B - C) - cos (B + C)) := by
        simp  [cos_sub,cos_add]; ring
      _ = 1 / 2 * (cos (B - C) - cos (π - A)) := by
        have : B + C = π - A := by rw [←hsum]; ring;
        simp [this]
      _ = 1 / 2 * (cos (B - C) + cos A) := by simp [cos_pi_sub]
  rw [h₁]
  have : sin A + 1 / 2 * (cos (B - C) + cos A)= √5 / 2 * (2 / √5 * sin A + 1 / √5 *cos A) + 1 / 2 * cos (B - C) := by
    rw [mul_add]
    nth_rw 2 [add_comm]
    rw [← add_assoc, add_right_cancel_iff]
    rw [mul_add,← mul_assoc,← mul_div_assoc]
    apply Eq.symm
    calc
      √5 / 2 * 2 / √5 * sin A + √5 / 2 * (1 / √5 * cos A) = sin A + √5 / 2 * (1 / √5 * cos A) := by
        aesop
      _ = sin A + 1 / 2 * cos A := by ring_nf; simp_all
  rw [this]
  have h' : 2 / √5 = cos (arccos (2 / √5)) := by
    apply Eq.symm
    apply cos_arccos
    exact le_trans (by aesop) (div_nonneg (by linarith) (sqrt_nonneg _))
    rw [div_le_one,le_sqrt]
    repeat linarith
    simp
  have h'' : 1 / √5 = sin (arccos (2 / √5)) := by
    rw [sin_arccos]
    apply Eq.symm
    rw [sqrt_eq_iff_mul_self_eq_of_pos]
    ring_nf
    norm_num
    rw [one_div_pos]
    norm_num
  nth_rw 1 [h', h'']
  rw [add_comm (cos (arccos (2 / √5)) * sin A), ← sin_add]

/-- Among all triangles $ABC,$ find the maximum value of $\sin A + \sin B \sin C.$-/
theorem precalculus_4110 : (∀ (A B C : ℝ), A + B + C = π → sin A + sin B * sin C ≤ (1 + √5) / 2)
          ∧ ∃ A, ∃ B, ∃ C, A + B + C = π ∧ sin A + sin B * sin C = (1 + √5) / 2 := by
  constructor
  · intros A B C hsum
    -- Substituting `sin A + sin B * sin C` by `√5 / 2 * sin (arccos (2 / √5) + A) + 1 / 2 * cos (B - C)`.
    rw [p98' hsum]
    nth_rw 3 [add_comm]
    -- `√5 / 2 * sin (arccos (2 / √5) + A) ≤  √5 / 2` because of `sin x ≤ 1`.  
    have h₁ : √5 / 2 * sin (arccos (2 / √5) + A) ≤ √5 / 2 := by
      nth_rw 2 [← one_mul (√5 / 2)]; norm_num
      exact sin_le_one _
    -- `1 / 2 * cos (B - C) ≤ 1 / 2` because of `cos x ≤ 1`.   
    have h₂ : 1 / 2 * cos (B - C) ≤ 1 / 2 := by
      nth_rw 2 [← one_mul (1 / 2)]; norm_num
      exact cos_le_one _
    rw [add_div]
    apply add_le_add h₁ h₂
  · -- The maximum value can be obtained when `A := π / 2 - arccos (2 / √5)`, 
    -- `B := π / 4 + arccos (2 / √5) / 2`, and `C := π / 4 + arccos (2 / √5) / 2`.
    let A := π / 2 - arccos (2 / √5)
    let B := π / 4 + arccos (2 / √5) / 2
    let C := π / 4 + arccos (2 / √5) / 2
    use A, B, C
    have hsum : A + B + C = π := by ring
    constructor
    · ring
    · rw [p98' hsum]
      dsimp [A,B,C]
      norm_num; ring
