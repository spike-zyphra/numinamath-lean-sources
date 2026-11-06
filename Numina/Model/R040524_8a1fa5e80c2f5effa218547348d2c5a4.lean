import Mathlib

open Real Set

theorem algebra_18775
    (valid : (ℝ × ℝ) → Prop)
    (h_valid : ∀ p : (ℝ × ℝ), valid p = (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1))
    (f : (ℝ × ℝ) → ℝ)
    (h_f : ∀ p : (ℝ × ℝ), f p = p.1 ^ 4 * p.2 + p.1 * p.2 ^ 4) :
    IsGreatest (f '' {p | valid p}) (1 / 12) := by
  constructor
  · -- Show 1/12 is attained, so it's in the image
    use ((3 + Real.sqrt 3) / 6, (3 - Real.sqrt 3) / 6)
    constructor
    · -- Show ((3 + Real.sqrt 3) / 6, (3 - Real.sqrt 3) / 6) is valid
      have h4 : valid (( (3 + Real.sqrt 3) / 6, (3 - Real.sqrt 3) / 6 ) ) := by
        rw [h_valid]
        constructor
        · -- Show (3 + Real.sqrt 3) / 6 ≥ 0
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        constructor
        · -- Show (3 - Real.sqrt 3) / 6 ≥ 0
          have h3 : Real.sqrt 3 ≤ 3 := by
            nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        · -- Show (3 + Real.sqrt 3) / 6 + (3 - Real.sqrt 3) / 6 = 1
          ring_nf
      exact h4
    · -- Show f(p) = 1/12 for the chosen point
      have h5 : f (( (3 + Real.sqrt 3) / 6, (3 - Real.sqrt 3) / 6 )) = 1 / 12 := by 
        rw [h_f]
        have hxy1 : ( (3 + Real.sqrt 3) / 6 ) * ( (3 - Real.sqrt 3) / 6 ) = 1 / 6 := by
          have h1 : ( (3 + Real.sqrt 3) / 6 ) * ( (3 - Real.sqrt 3) / 6 ) = ( (3 + Real.sqrt 3 ) * (3 - Real.sqrt 3) ) / 36 := by 
            ring_nf
          rw [h1]
          have h2 : (3 + Real.sqrt 3) * (3 - Real.sqrt 3) = (9 : ℝ) - (3 : ℝ) := by 
            have hsq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
            nlinarith
          rw [h2]
          norm_num 
        have hxy2 : ( (3 + Real.sqrt 3) / 6 ) + ( (3 - Real.sqrt 3) / 6 ) = (1 : ℝ) := by 
          ring_nf
        have hx4y1 : ( (3 + Real.sqrt 3) / 6 ) ^ 4 * ( (3 - Real.sqrt 3) / 6 ) + ( (3 + Real.sqrt 3) / 6 ) * ( (3 - Real.sqrt 3) / 6 ) ^ 4 = (1 / 12 : ℝ) := by 
          have h1 : ( (3 + Real.sqrt 3) / 6 ) + ( (3 - Real.sqrt 3) / 6 ) = (1 : ℝ) := hxy2
          have h2 : ( (3 + Real.sqrt 3) / 6 ) * ( (3 - Real.sqrt 3) / 6 ) = (1 / 6 : ℝ) := hxy1 
          have h3 : ( (3 + Real.sqrt 3) / 6 ) ^ 4 * ( (3 - Real.sqrt 3) / 6 ) + ( (3 + Real.sqrt 3) / 6 ) * ( (3 - Real.sqrt 3) / 6 ) ^ 4 = ( (3 + Real.sqrt 3) / 6 ) * ( (3 - Real.sqrt 3) / 6 ) * ( ( (3 + Real.sqrt 3) / 6 ) ^ 3 + ( (3 - Real.sqrt 3) / 6 ) ^ 3 ) := by 
            ring
          rw [h3]
          have h4 : ( (3 + Real.sqrt 3) / 6 ) ^ 3 + ( (3 - Real.sqrt 3) / 6 ) ^ 3 = (1 / 2 : ℝ) := by 
            have h5 : ( (3 + Real.sqrt 3) / 6 ) + ( (3 - Real.sqrt 3) / 6 ) = (1 : ℝ) := hxy2
            have h5' : ( (3 + Real.sqrt 3) / 6 ) * ( (3 - Real.sqrt 3) / 6 ) = (1 / 6 : ℝ) := h2
            have h6 : ( (3 + Real.sqrt 3) / 6 ) ^ 3 + ( (3 - Real.sqrt 3) / 6 ) ^ 3 = ( ( (3 + Real.sqrt 3) / 6 ) + ( (3 - Real.sqrt 3) / 6 ) ) ^ 3 - 3 * ( ( (3 + Real.sqrt 3) / 6 ) * ( (3 - Real.sqrt 3) / 6 ) ) * ( ( (3 + Real.sqrt 3) / 6 ) + ( (3 - Real.sqrt 3) / 6 ) ) := by ring 
            rw [h6, h5, h5']
            norm_num 
          rw [h4, h2]
          norm_num 
        linarith [hx4y1]
      linarith [ h5 ]
  · -- Show 1/12 is the greatest value
    intro r hr
    rcases hr with ⟨p, hp, hr⟩
    have hp2 : valid p := by 
      simpa using hp 
    have hp3 : 0 ≤ p.1 := by
      rw [h_valid] at hp2
      tauto
    have hp4 : 0 ≤ p.2 := by
      rw [h_valid] at hp2 
      tauto 
    have hp5 : p.1 + p.2 = 1 := by 
      rw [h_valid] at hp2 
      tauto 
    have hr1 : r = p.1 ^ 4 * p.2 + p.1 * p.2 ^ 4 := by 
      have h2 : f p = p.1 ^ 4 * p.2 + p.1 * p.2 ^ 4 := h_f p 
      linarith [ hr, h2 ] 
    have h1 : p.2 = 1 - p.1 := by 
      linarith 
    rw [hr1]
    rw [h1]
    nlinarith [sq_nonneg (p.1 - (3 + Real.sqrt 3) / 6), sq_nonneg (p.1 - (3 - Real.sqrt 3) / 6), sq_nonneg (p.1 * (1 - p.1) - 1 / 6), sq_nonneg (p.1 - (1/2)), sq_nonneg (p.1 - (3 + Real.sqrt 3) / 6), sq_nonneg (p.1 - (3 - Real.sqrt 3) / 6), Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]