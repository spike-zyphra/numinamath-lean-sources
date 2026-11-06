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

  have h3 : dotProduct (a + b) (a + k • b) = dotProduct a a + k * (dotProduct a b) + dotProduct b a + k * (dotProduct b b) := by
    simp [dotProduct, Finset.sum]
    <;> ring_nf <;> simp [Matrix.vec2_dotProduct, Fin.sum_univ_two]
    <;> ring_nf
    <;> norm_num
    <;> aesop
    <;> aesop
    <;> aesop
    <;> aesop
    <;> tauto
    <;> norm_num
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> norm_num
    <;> norm_num
    <;> ring_nf
    <;> norm_num
    <;> norm_num
  have h31 : dotProduct a a = 1 := by
    have h_eq1 : dotProduct a a = ‖a‖ ^2 := by
      simp [←real_inner_self_eq_norm_sq, dotProduct]
      <;> norm_num
      <;> aesop
    rw [h_eq1, h₀]
    all_goals norm_num
  have h32 : dotProduct b b = 4 := by
    have h_eq1 : dotProduct b b = ‖b‖ ^2 := by
      simp [←real_inner_self_eq_norm_sq, dotProduct]
      <;> norm_num
      <;> aesop
    rw [h_eq1, h₁]
    all_goals norm_num
  have h33 : dotProduct a b = 1 := by
    rw [h₂, Real.cos_pi_div_three, h₀, h₁]
    norm_num
  have h34 : dotProduct b a = 1 := by
    have h_eq1 : dotProduct b a = dotProduct a b := by
      simp [dotProduct, Finset.sum]
      <;> ring_nf
      <;> norm_num
      <;> aesop
      <;> aesop
    rw [h_eq1, h33]
  rw [h3, h31, h33, h34, h32]
  constructor
  · -- Assume the dot product is zero, derive k = -2/5
    intro h_eq
    nlinarith
  · -- Assume k = -2/5, derive the dot product is zero
    intro h_eq
    rw [h_eq]
    nlinarith