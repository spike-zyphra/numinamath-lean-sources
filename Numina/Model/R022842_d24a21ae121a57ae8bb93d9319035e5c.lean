import Mathlib

open Real Set
open scoped Real

theorem algebra_110184 (f : ℝ → ℝ) (hf : f = λ x => sin x ^ 2 + cos x) :
    range f = {x | -1 ≤ x ∧ x ≤ 5/4} := by
  ext y
  simp [hf]
  constructor
  · -- Assume y ∈ range f, we need to prove y ∈ {x | -1 ≤ x ∧ x ≤ 5/4}
    rintro ⟨x, hx⟩
    have h1 : -1 ≤ cos x ∧ cos x ≤ 1 := by 
      constructor
      · linarith [neg_one_le_cos x]
      · linarith [cos_le_one x]
    have h2 : sin x ^ 2 = 1 - cos x ^ 2 := by 
      rw [←Real.sin_sq_add_cos_sq x]
      linarith
    have h3 : -1 ≤ y := by 
      rw [show sin x ^ 2 + cos x = - (cos x) ^ 2 + (cos x) + 1 by
        rw [h2]
        ring] at hx
      nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x - 2), h1.1, h1.2]
    have h4 : y ≤ 5/4 := by
      rw [show sin x ^ 2 + cos x = - (cos x) ^ 2 + (cos x) + 1 by
        rw [h2]
        ring] at hx
      nlinarith [sq_nonneg (cos x - 1/2), sq_nonneg (cos x - 1/2), h1.1, h1.2]
    constructor <;> linarith
  · -- Assume y ∈ {x | -1 ≤ x ∧ x ≤ 5/4}, we need to prove y ∈ range f
    rintro ⟨hy1, hy2⟩
    use Real.arccos ( (1 - Real.sqrt (5 - 4 * y)) / 2 )
    have h5 : -1 ≤ ( (1 - Real.sqrt (5 - 4 * y)) / 2 ) ∧ ( (1 - Real.sqrt (5 - 4 * y)) / 2 ) ≤ 1 := by
      have h11 : 0 ≤ Real.sqrt (5 - 4 * y) := by apply Real.sqrt_nonneg
      have h22 : (Real.sqrt (5 - 4 * y)) ≤ 3 := by
        have h33 : Real.sqrt (5 - 4 * y) ≤ Real.sqrt (9: ℝ) := Real.sqrt_le_sqrt (by nlinarith)
        have h44 : Real.sqrt (9: ℝ) = 3 := by
          rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
        linarith [h44]
      constructor
      · -- Show that -1 ≤ (1 - Real.sqrt (5 - 4 * y)) / 2
        nlinarith [Real.sqrt_nonneg (5 - 4 * y), h22]
      · -- Show that (1 - Real.sqrt (5 - 4 * y)) / 2 ≤ 1
        nlinarith [Real.sqrt_nonneg (5 - 4 * y), h22]
    have h6 : sin (Real.arccos ( (1 - Real.sqrt (5 - 4 * y)) / 2 )) ^ 2 + cos (Real.arccos ( (1 - Real.sqrt (5 - 4 * y)) / 2 )) = y := by
      have h7 : cos (Real.arccos ( (1 - Real.sqrt (5 - 4 * y)) / 2 )) = (1 - Real.sqrt (5 - 4 * y)) / 2 := by 
        apply Real.cos_arccos 
        linarith [h5.1, h5.2]
        linarith [h5.1, h5.2]
      have h8 : sin (Real.arccos ( (1 - Real.sqrt (5 - 4 * y)) / 2 )) ^ 2 = 1 - ( (1 - Real.sqrt (5 - 4 * y)) / 2 ) ^ 2 := by 
        have h9 : sin (Real.arccos ( (1 - Real.sqrt (5 - 4 * y)) / 2 )) ^ 2 + cos (Real.arccos ( (1 - Real.sqrt (5 - 4 * y)) / 2 )) ^ 2 = 1 := by 
          exact Real.sin_sq_add_cos_sq (Real.arccos ( (1 - Real.sqrt (5 - 4 * y)) / 2 ) )
        rw [h7] at h9
        nlinarith
      rw [h7, h8]
      nlinarith [ Real.sqrt_nonneg (5 - 4 * y), Real.sq_sqrt (show (0 : ℝ) ≤ (5 - 4 * y) by nlinarith) ]
    linarith [h6]