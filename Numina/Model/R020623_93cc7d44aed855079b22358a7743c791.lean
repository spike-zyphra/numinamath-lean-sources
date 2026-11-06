import Mathlib

open Real
open scoped Real

theorem inequalities_327722 (A B C : Real) (hA : A ∈ Set.Ioo 0 (π / 2)) (hB : B ∈ Set.Ioo 0 (π / 2))
    (hC : C ∈ Set.Ioo 0 (π / 2)) (hABC : A + B + C = π) :
    cos A + cos B + cos C ≥ 2 * (cos A * cos B + cos B * cos C + cos C * cos A) := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have h1 : cos A > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [hA1]
    · linarith [hA2]
  have h2 : cos B > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [hB1]
    · linarith [hB2]
  have h3 : cos C > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [hC1]
    · linarith [hC2]

  have h4 : sin A > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [hA1]
    · linarith [hA2, Real.pi_gt_three]
  have h5 : sin B > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [hB1]
    · linarith [hB2, Real.pi_gt_three]
  have h6 : sin C > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [hC1]
    · linarith [hC2, Real.pi_gt_three]

  have h7 : C = π - A - B := by
    linarith

  have h8 : cos C = -cos (A + B) := by
    rw [show C = π - (A + B) by linarith [h7]]
    have h12 : cos (π - (A + B)) = -cos (A + B) := by 
      rw [cos_pi_sub]
      all_goals ring_nf
    linarith

  have h9 : cos (A + B) = cos A * cos B - sin A * sin B := by
    rw [cos_add]

  have h10 : cos C = - (cos A * cos B - sin A * sin B) := by
    rw [h8, h9]

  rw [h10]
  nlinarith [sq_nonneg (cos A - cos B), sq_nonneg (cos B + cos A - 1), sq_nonneg ((sin A - sin B)), 
            Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C, 
            mul_pos h1 h2, mul_pos h1 h4, mul_pos h2 h5, mul_pos h4 h5, 
            Real.sin_sq_add_cos_sq (A + B), Real.sin_pos_of_pos_of_lt_pi (show 0 < A + B by linarith) (by linarith [Real.pi_gt_three, show A < π / 2 by linarith, show B < π / 2 by linarith, hABC]
            ), 
            Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq (A + B),
            sq_nonneg (A + B - π / 2)
]