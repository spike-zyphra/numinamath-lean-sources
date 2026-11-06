import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_11901 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (arccos (x / 2))^2 + π * arcsin (x / 2) - (arcsin (x / 2))^2 +
    (π^2 / 12) * (x^2 + 6 * x + 8)) :
  image f (Icc (-2) 2) = Icc (π^2 / 4) (9 * π^2 / 4) := by
  have h1 : ∀ x, f x = (π ^ 2 / 12) * (x + 3) ^ 2 + π ^ 2 / 6 := by
    intro x
    rw [h₀ x]
    have h2 : arccos (x / 2) = π / 2 - arcsin (x / 2) := by
      rw [Real.arccos_eq_pi_div_two_sub_arcsin]
      <;> ring_nf
      <;> try linarith
    rw [h2]
    have h12 : (π / 2 - arcsin (x / 2)) ^ 2 - (arcsin (x / 2)) ^ 2 + π * arcsin (x / 2) = π ^ 2 / 4 := by
      nlinarith [Real.pi_pos, sq_nonneg (arcsin (x / 2) - π / 4)]
    nlinarith [Real.pi_pos, h12, Real.pi_pos]
  ext y
  simp only [mem_image, mem_setOf_eq, Set.mem_Icc, image]
  constructor
  · -- Prove that the image is contained in the interval
    rintro ⟨x, hx, rfl⟩
    rw [h1 x]
    have hx0 : -2 ≤ x := by linarith [hx.1]
    have hx1 : x ≤ 2 := by linarith [hx.2]
    have h16_a : 0 ≤ (x + 3) ^ 2 := sq_nonneg (x + 3)
    have h16_b : π ^ 2 / 4 ≤ (π ^ 2 / 12) * (x + 3) ^ 2 + π ^ 2 / 6 := by
      nlinarith [sq_nonneg (x + 3 - 1), Real.pi_pos, sq_nonneg (x + 2), sq_nonneg (x - 2), mul_nonneg Real.pi_nonneg Real.pi_nonneg, Real.pi_nonneg, Real.pi_pos]
    have h16_c : (π ^ 2 / 12) * (x + 3) ^ 2 + π ^ 2 / 6 ≤ 9 * π ^ 2 / 4 := by
      have h510 : x + 3 ≤ (2 + 3 : ℝ) := by linarith
      have h420 : (x + 3) ^ 2 ≤ (5) ^ 2 := by nlinarith [sq_nonneg (x + 3 - 5), sq_nonneg (x - 2)]
      nlinarith [sq_nonneg (x - 2), h420, mul_nonneg Real.pi_nonneg Real.pi_nonneg, Real.pi_nonneg, Real.pi_pos, Real.pi_nonneg]
    constructor
    · -- Show the lower bound
      nlinarith
    · -- Show the upper bound
      nlinarith
  · -- Prove the converse: any element in the interval is attained
    rintro ⟨hy1, hy2⟩
    use Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) - 3
    constructor
    · -- Show the element is in the interval
      have h4_nonneg : 0 ≤ ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 := by
        have h80 : π ^ 2 > 0 := by positivity
        have h81 : (y * 12 - π ^ 2 * 2) ≥ 0 := by
          nlinarith [show π ^ 2 / 4 ≤ y from by linarith, Real.pi_pos, sq_nonneg (π^2), sq_nonneg (y * 12)]
        have h82 : ((y * 12 - π ^ 2 * 2) ) / π ^ 2 ≥ 0 := by
          apply div_nonneg
          nlinarith
          nlinarith
        linarith [h82]
      have h15_a : (Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2)) ^ 2 = ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 := Real.sq_sqrt (by linarith)
      have h15_b : Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) ≥ 1 := by
        have h40_a : ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 ≥ (1 : ℝ) := by
          have h80 : π ^ 2 > 0 := by positivity
          have h81 : ( (y * 12 - π ^ 2 * 2) ) ≥ π ^ 2 := by
            nlinarith [show π ^ 2 / 4 ≤ y by linarith, Real.pi_pos, Real.pi_pos]
          have h081 : ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 ≥ (π^2) / π^2 := by
            have h800 : 0 < π ^ 2 := by positivity
            apply (div_le_div_right h800).mpr
            nlinarith
          have h082 : (π^2) / π^2 = (1 : ℝ) := by
            have h800 : π ^ 2 > 0 := by positivity
            field_simp
          nlinarith
        have h40_b : (Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) ) ≥ (Real.sqrt ( (1 : ℝ) )) := Real.sqrt_le_sqrt (by nlinarith [h40_a])
        have h41_a : Real.sqrt (1 : ℝ) = (1 : ℝ) := Real.sqrt_one
        nlinarith [show Real.sqrt (1 : ℝ) = (1 : ℝ) by rw [Real.sqrt_one], h40_b, h15_a]
      have h15_c : Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) ≤ ( (5 : ℝ) ) := by
        -- Show sqrt(( (y * 12 - π ^ 2 * 2) ) / π ^ 2) ≤ 5
        have h40_a : ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 ≤ ( (25 : ℝ) ) := by
          -- Show ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 ≤ ( (25 : ℝ) )
          have h80 : π ^ 2 > 0 := by positivity
          have h81 : ( (y * 12 - π ^ 2 * 2) ) ≤ ( (25 * π ^ 2) ) := by
            nlinarith [show y ≤ 9 * π ^ 2 / 4 by linarith, Real.pi_nonneg, Real.pi_nonneg, Real.pi_pos, sq_nonneg (y), sq_nonneg (π ^ 2 * 2), sq_nonneg (π ^ 2 * 25)]
          have h82 : ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 ≤ ( (25 * π ^ 2) ) / π ^ 2 := by
            apply (div_le_div_right (by positivity)).mpr
            nlinarith [Real.pi_nonneg, sq_nonneg (π^2 * 25), sq_nonneg (π^2 * 25)]
          have h83 : ( (25 * π ^ 2) ) / π ^ 2 = ( (25 : ℝ) ) := by
            have h800 : π ^ 2 > 0 := by positivity
            field_simp
            <;> nlinarith
          nlinarith
        have h40_b : (Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) ) ≤ (Real.sqrt (25 : ℝ)) := Real.sqrt_le_sqrt (by nlinarith [h40_a])
        have h40_c : Real.sqrt (25 : ℝ) = (5 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          all_goals nlinarith
        nlinarith [h40_b, h40_c, h15_a]
      constructor
      · -- Show that -2 ≤ Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) - 3
        nlinarith [Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2), h15_a, h15_b, h15_c, Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2), Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2)]
      · -- Show that Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) - 3 ≤ 2
        nlinarith [Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2), h15_a, h15_b, h15_c, Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2), Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2)]
    · -- Show that f (Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) - 3) = y
      rw [h1]
      have h4_nonneg : 0 ≤ ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 := by
        have h80 : π ^ 2 > 0 := by positivity
        have h81 : ( (y * 12 - π ^ 2 * 2) ) ≥ 0 := by
          nlinarith [show π ^ 2 / 4 ≤ y from by linarith, Real.pi_pos, sq_nonneg (π ^ 2), sq_nonneg (y * 12)]
        have h82 : ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 ≥ 0 := by
          apply div_nonneg
          nlinarith
          nlinarith
        linarith [h82]
      have h76_c : ( (Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) - 3) + 3) ^ 2 = ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 := by
        have h15_a : (Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) ) ^ 2 = ( (y * 12 - π ^ 2 * 2) ) / π ^ 2 := Real.sq_sqrt (by linarith)
        have h765 : (Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) - 3 + 3) ^ 2 = (Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) ) ^ 2 := by ring_nf
        nlinarith [Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2), h765, h15_a, Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2), Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2)]
      have h76_d : (π ^ 2 / 12) * ( (Real.sqrt (( (y * 12 - π ^ 2 * 2) ) / π ^ 2) - 3) + 3) ^ 2 + (π ^ 2 / 6) = y := by
        rw [h76_c]
        have h15_a : π ^ 2 > 0 := by positivity
        field_simp [h15_a]
        nlinarith [mul_nonneg Real.pi_nonneg Real.pi_nonneg, Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2), h76_c, h4_nonneg, Real.sqrt_nonneg (( (y * 12 - π ^ 2 * 2) ) / π ^ 2)]
      linarith [h76_d]
  all_goals try nlinarith
  <;> try tauto