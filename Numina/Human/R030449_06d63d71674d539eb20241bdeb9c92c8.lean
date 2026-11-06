import Mathlib


theorem algebra_446119_1 (a b : EuclideanSpace ℝ (Fin 2))
  (h₀: ‖a‖ = 1)
  (h₁: ‖b‖ = 2)
  (h₂: dotProduct a b = ‖a‖ * ‖b‖ * Real.cos (Real.pi /3 )):
  ‖2 • a - b‖ = 2 := by

  rw [norm_eq_sqrt_real_inner]

  have h1: inner (2 • a - b) (2 • a - b) = 4 * ‖a‖^2 + ‖b‖^2
    - 4 * (dotProduct a b) := by
    simp only [PiLp.inner_apply, PiLp.sub_apply, PiLp.smul_apply, nsmul_eq_mul,
     Nat.cast_ofNat, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
     Fin.isValue, ← real_inner_self_eq_norm_sq, Matrix.vec2_dotProduct]
    ring

  have h2: dotProduct a b = 1 := by
    rw [h₂, Real.cos_pi_div_three, h₀, h₁]
    norm_num

  have: √(4:ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq]
    all_goals norm_num
  rw [h1, h2, h₀, h₁]
  norm_num [this]


theorem algebra_446119_2 (a b : EuclideanSpace ℝ (Fin 2)) (k:ℝ)
  (h₀: ‖a‖ = 1)
  (h₁: ‖b‖ = 2)
  (h₂: dotProduct a b = ‖a‖ * ‖b‖ * Real.cos (Real.pi /3 )):
  dotProduct (a + b) (a + k • b) = 0 ↔ k = -2/5 := by

  have h1: dotProduct (a+b) (a + k • b) = ‖a‖^2 + k*‖b‖^2  +
    (k+1) * (dotProduct a b) := by
    simp only [Matrix.vec2_dotProduct, Fin.isValue, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, ←real_inner_self_eq_norm_sq,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two]
    ring

  have h2: dotProduct a b = 1 := by
    rw [h₂, Real.cos_pi_div_three, h₀, h₁]
    norm_num

  rw [h1, h2, h₀, h₁]
  constructor <;> intro h
  all_goals linarith only [h]