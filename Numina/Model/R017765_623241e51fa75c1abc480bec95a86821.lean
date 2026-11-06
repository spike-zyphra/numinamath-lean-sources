import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_164886 {f : ℝ → ℝ}
  (h : ∀ x ≠ 0, x ≠ 1 → f (x / (x - 1)) = 1 / x)
  (θ : ℝ) (hθ : θ ∈ Ioo 0 (π / 2)) :
  f (1 / (cos θ) ^ 2) = sin θ ^ 2 := by
  rcases hθ with ⟨h1, h2⟩
  have h3 : sin θ > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h4 : cos θ > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith
  have h3' : sin θ ^ 2 + cos θ ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq θ
  have hx1 : (1 / (sin θ) ^ 2 : ℝ) ≠ 0 := by
    by_contra h8
    have h9 : sin θ ^ 2 = 0 := by
      field_simp at h8
      <;> nlinarith
    have h10 : sin θ = 0 := by
      nlinarith
    linarith
  have hx2 : (1 / (sin θ) ^ 2 : ℝ) ≠ 1 := by
    by_contra h11
    have h6 : sin θ ^ 2 = 1 := by 
      field_simp at h11
      all_goals
      nlinarith
    have h7 : sin θ ^ 2 < 1 := by
      have h8 : sin θ < 1 := by 
        have h9 : sin θ < sin (π / 2) := by
          apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
          all_goals
            linarith
        have h10 : sin (π / 2) = 1 := by 
          rw [sin_pi_div_two]
        nlinarith
      nlinarith [sq_nonneg (sin θ - 1)]
    nlinarith
  -- Apply the functional equation with x = 1/(sin^2 θ)
  specialize h (1 / (sin θ) ^ 2) hx1 hx2
  have eq1 : (1 / (sin θ) ^ 2 : ℝ) / ((1 / (sin θ) ^ 2 : ℝ) - 1) = 1 / (cos θ) ^ 2 := by
    have h5 : sin θ ^ 2 > 0 := by
      nlinarith [sq_pos_of_pos h3]
    have h6 : cos θ ^ 2 > 0 := by
      nlinarith [sq_pos_of_pos h4]
    have h7 : 1 - sin θ ^ 2 = cos θ ^ 2 := by 
      have h8 : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      nlinarith
    field_simp [show sin θ ≠ 0 by nlinarith, show cos θ ≠ 0 by nlinarith, show (1 : ℝ) - sin θ ^ 2 ≠ 0 by
      nlinarith [h6]
    ]
    <;> nlinarith [sq_pos_of_pos h3, sq_pos_of_pos h4, h7]
  rw [eq1] at h 
  field_simp at h ⊢
  <;> nlinarith [sq_pos_of_pos h3, sq_pos_of_pos h4, Real.sin_sq_add_cos_sq θ]