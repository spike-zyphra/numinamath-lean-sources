import Mathlib

open Real Set
open scoped Real

theorem algebra_159949 (f : ℝ → ℝ)
  (h₀ : ∀ θ, f θ = sqrt (1 - cos θ + sin θ) + sqrt (cos θ + 2) + sqrt (3 - sin θ)) :
  IsGreatest (image f (Icc 0 Real.pi)) (3 * sqrt 2) := by
  constructor
  · -- Prove that 3 * sqrt 2 is attained at θ = Real.pi / 2
    use Real.pi / 2
    constructor
    · -- Show Real.pi / 2 is in the interval
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show the value equals 3 * sqrt 2
      have h1 : sin (Real.pi / 2 : ℝ) = 1 := by
        exact sin_pi_div_two
      have h2 : cos (Real.pi / 2 : ℝ) = 0 := by
        exact cos_pi_div_two
      rw [h₀]
      rw [h1, h2]
      have h3 : sqrt (1 - (0 : ℝ) + (1 : ℝ)) = Real.sqrt 2 := by
        rw [show (1 - (0 : ℝ) + (1 : ℝ) : ℝ) = (2 : ℝ) by norm_num]
        all_goals norm_num
      have h4 : sqrt ((0 : ℝ) + (2 : ℝ)) = Real.sqrt 2 := by 
        rw [show (0 + (2 : ℝ) : ℝ) = (2 : ℝ) by norm_num]
        all_goals norm_num
      have h5 : sqrt ((3 - (1 : ℝ) : ℝ)) = Real.sqrt 2 := by 
        rw [show (3 - (1 : ℝ) : ℝ) = (2 : ℝ) by norm_num]
        all_goals norm_num
      rw [h3, h4, h5]
      ring_nf <;> norm_num
      all_goals norm_num
  · -- We need to prove 3 * sqrt 2 is an upper bound
    intro y hy
    rcases hy with ⟨θ, hθ, rfl⟩
    rw [h₀ θ]
    have h1 : 0 ≤ θ := by
      linarith [hθ.1, Real.pi_pos]
    have h2 : θ ≤ Real.pi := by
      linarith [hθ.2, Real.pi_pos]
    have h6 : 0 ≤ (1 - cos θ + sin θ : ℝ) := by
      have hcos : -1 ≤ cos θ ∧ cos θ ≤ 1 := by
        constructor
        · apply Real.neg_one_le_cos
        · apply Real.cos_le_one
      have hsin : -1 ≤ sin θ ∧ sin θ ≤ 1 := by
        constructor
        · apply Real.neg_one_le_sin
        · apply Real.sin_le_one
      have h1 : 0 ≤ sin θ := by
        apply Real.sin_nonneg_of_nonneg_of_le_pi
        · linarith -- θ ≥ 0
        · linarith -- θ ≤ π
      nlinarith
    have hcos_add_1 : 0 ≤ (cos θ + 2 : ℝ) := by
      have hcos : -1 ≤ cos θ ∧ cos θ ≤ 1 := by
        constructor
        · apply Real.neg_one_le_cos
        · apply Real.cos_le_one
      nlinarith
    have hsin_sub_1 : 0 ≤ (3 - sin θ : ℝ) := by
      have hsin : -1 ≤ sin θ ∧ sin θ ≤ 1 := by
        constructor
        · apply Real.neg_one_le_sin
        · apply Real.sin_le_one
      nlinarith
    have h3 : sqrt (1 - cos θ + sin θ) + sqrt (cos θ + 2) + sqrt (3 - sin θ) ≤ 3 * sqrt 2 := by
      nlinarith [sq_nonneg (sqrt (1 - cos θ + sin θ) - sqrt (cos θ + 2)), sq_nonneg (sqrt (1 - cos θ + sin θ) - sqrt (3 - sin θ)), sq_nonneg (sqrt (cos θ + 2) - sqrt (3 - sin θ)), 
      Real.sqrt_nonneg 2, Real.sqrt_nonneg (1 - cos θ + sin θ), Real.sqrt_nonneg (cos θ + 2), Real.sqrt_nonneg (3 - sin θ),
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ (1 - cos θ + sin θ : ℝ) by assumption),
      Real.sq_sqrt (show (0 : ℝ) ≤ (cos θ + 2 : ℝ) by assumption),
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 - sin θ : ℝ) by assumption),
      Real.cos_sq_add_sin_sq θ, 
      Real.sin_sq_add_cos_sq θ, 
      Real.sin_le_one θ, 
      Real.cos_le_one θ,
      Real.sin_nonneg_of_nonneg_of_le_pi (show (0 : ℝ) ≤ θ by assumption) (show θ ≤ Real.pi by assumption)
      ]
    linarith [h3, Real.sqrt_nonneg 2, Real.sqrt_nonneg (1 - cos θ + sin θ), Real.sqrt_nonneg (cos θ + 2), Real.sqrt_nonneg (3 - sin θ)
    ]