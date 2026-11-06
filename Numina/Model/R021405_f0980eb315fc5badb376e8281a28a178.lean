import Mathlib

open Real Set
open scoped Real

theorem algebra_3980 (θ : Real) (hθ : θ ∈ Ioo 0 (π / 2)) :
  3 * sin θ + 4 * cos θ ≤ 5 ∧
  ∃ θ : Real, θ ∈ Ioo 0 (π / 2) ∧ 3 * sin θ + 4 * cos θ = 5 := by

  rcases hθ with ⟨h1, h2⟩
  constructor
  · -- Prove the inequality
    have h3 : (3 * sin θ + 4 * cos θ) ^ 2 ≤ (3 ^ 2 + 4 ^ 2) * (sin θ ^ 2 + cos θ ^ 2) := by
      nlinarith [sq_nonneg (3 * cos θ - 4 * sin θ), Real.sin_sq_add_cos_sq θ]
    have h4 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq θ
    nlinarith [Real.sin_le_one θ, Real.cos_le_one θ, sq_nonneg (3 * sin θ + 4 * cos θ - 5), sq_nonneg (sin θ - 3 / 5), sq_nonneg (cos θ - 4 / 5), sq_nonneg (sin θ ^ 2 + cos θ ^ 2 - 1)]
  · -- Show existence of angle achieving maximum
    use Real.arcsin (3 / 5)
    have h8 : (0 : Real) < Real.arcsin (3 / 5) := by
      apply Real.arcsin_pos.mpr
      norm_num
    have h9 : Real.arcsin (3 / 5) < Real.pi / 2 := by
      apply Real.arcsin_lt_pi_div_two.mpr
      norm_num
    constructor
    · -- Show angle is in interval (0, π/2)
      exact ⟨h8, h9⟩
    · -- Show expression equals 5
      have h10 : sin (Real.arcsin (3 / 5) : Real) = (3 / 5 : Real) := by
        apply Real.sin_arcsin
        all_goals norm_num
      have h11 : cos (Real.arcsin (3 / 5) : Real) = (4 / 5 : Real) := by
        have h12 : cos (Real.arcsin (3 / 5) : Real) = Real.sqrt (1 - (3 / 5 : Real) ^ 2) := by
          rw [Real.cos_arcsin]
        rw [h12]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h10, h11]
      norm_num