import Mathlib


open BigOperators Real Set


lemma lemma_1 (x y z : ℝ) (h₀ : x * y * z^2 = 2) (h₁ : x = y) (h₂ : x > 0) :
    x^2 + y^2 + z^2 ≥ 4 := by
  have h4 : y = x := by linarith
  rw [h4] at h₀
  have eq1 : x^2 * z^2 = 2 := by
    nlinarith [h₀, sq_nonneg (x * z) ]
  have h4 : z^2 ≥ 0 := sq_nonneg z
  have eq2 : 0 < x := h₂
  have h5 : 0 < x^2 := by nlinarith
  have eq5 : x^2 + x^2 + z^2 ≥ 4 := by
    have eq3 : z^2 * x^2 = 2 := by linarith
    have eq4 : z^2 = 2 / (x^2 ) := by
      have hx4 : x^2 ≠ 0 := by nlinarith
      field_simp
      <;> nlinarith
    rw [eq4]
    have eq6 : x^2 + x^2 + (2 / (x^2 )) ≥ 4 := by
      have hx21 : 0 < x^2 := h5
      have eq7 : (x^2 + x^2 + (2 / (x^2 )) - 4 ) ≥ 0 := by
        have h7 : (x^2 + x^2 + (2 / (x^2 )) - 4 ) = (2 * (x^2 - 1)^2 ) / (x^2 ) := by
          field_simp
          <;> ring
        rw [h7]
        have h8 : 2 * (x^2 - 1)^2 ≥ 0 := by
          have hx29 : (x^2 - 1)^2 ≥ 0 := sq_nonneg (x^2 - 1)
          nlinarith
        apply div_nonneg
        all_goals nlinarith
      linarith
    linarith
  have eq6 : x^2 + y^2 + z^2 = 2 * x^2 + z^2 := by
    have eq7 : y^2 = x^2 := by
      rw [show y = x by linarith [h₁]]
    nlinarith [eq7]
  have hx5 : 2 * x^2 + z^2 ≥ 4 := by
    linarith [eq5]
  have hx6 : x^2 + y^2 + z^2 ≥ 4 := by
    linarith [eq6, hx5]
  linarith


theorem algebra_20868 (P : EuclideanSpace ℝ (Fin 3)) (hP : P 0 * P 1 * P 2 ^ 2 = 2) :
    IsLeast {d | ∃ P : EuclideanSpace ℝ (Fin 3), P 0 * P 1 * P 2 ^ 2 = 2 ∧ d = dist P 0} 2 := by
  constructor
  · -- First, we show that 2 belongs to the set
    use λ i =>
      match i with
      | 0 => (1 : ℝ)
      | 1 => (1 : ℝ)
      | 2 => (Real.sqrt 2 : ℝ)
      | _ => (0 : ℝ)
    constructor
    · -- Show that the point (1, 1, sqrt(2)) satisfies the constraint
      simp [Fin.sum_univ_three]
      <;> ring_nf
      <;> norm_num
      <;> ring
    · -- Show that the distance from the point (1, 1, sqrt(2)) to the origin is 2
      simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three]
      have h1 : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      ring_nf <;> norm_num [h1] <;> ring
  · -- Now we show that 2 is the minimum distance
    intro d hd
    rcases hd with ⟨P, hp1, hp2⟩
    have h2 : dist P (0 : EuclideanSpace ℝ (Fin 3) ) = Real.sqrt ((P 0) ^2 + (P 1) ^2 + (P 2) ^ 2) := by
      have h1 : dist P (0 : EuclideanSpace ℝ (Fin 3) ) = Real.sqrt (∑ i : Fin 3, (P i - (0 : EuclideanSpace ℝ (Fin 3)) i) ^ 2) := by
        simp [dist_eq_norm, EuclideanSpace.norm_eq]
        <;> ring_nf <;> simp
        <;> ring
      rw [h1]
      simp [Fin.sum_univ_three]
      <;> ring_nf <;> simp
      <;> ring
    have h22 : d = Real.sqrt ((P 0) ^2 + (P 1) ^2 + (P 2) ^2) := by 
      linarith [h2, hp2]
    have h3 : (P 0) ^2 + (P 1) ^2 + (P 2) ^2 ≥ 4 := by
      have hp11 : P 0 * P 1 * (P 2 : ℝ) ^ 2 = 2 := hp1
      nlinarith [sq_nonneg (P 0 - 1), sq_nonneg (P 1 - 1), sq_nonneg (P 2 ^ 2 - 2), sq_nonneg (P 0 - P 1), sq_nonneg (P 0 * (P 2 ^ 2) - 2), sq_nonneg ((P 0) * (P 1) - 1), sq_nonneg ((P 0) ^2 - 1), sq_nonneg ((P 1) ^2 - 1), mul_pos (show (0 : ℝ) < 2 by norm_num) (show (0 : ℝ) < 2 by norm_num), sq_nonneg (P 2 ^2 - 2)]
    have h4 : Real.sqrt ((P 0) ^2 + (P 1) ^2 + (P 2) ^2) ≥ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (h3)
    have h51 : Real.sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h51] at h4
    have h61 : d ≥ 2 := by
      rw [h22]
      linarith [h4]
    linarith