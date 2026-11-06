import Mathlib

theorem algebra_224801 :
    {x : ℝ | x > 0 ∧ (x * 2014 ^ ((1 : ℝ) / x) + (1 / x) * 2014 ^ x) / 2 = 2014} = 
    {1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Simplify an element `x` satisfies the equation to `x = 1`.
    intro h
    rcases h with ⟨hx1, heq⟩
    have h1 : x * (2014 : ℝ) ^ ((1 : ℝ) / x) + (1 / x) * (2014 : ℝ) ^ x = 4028 := by
      linarith
    have h2 : x * (2014 : ℝ) ^ ((1 : ℝ) / x) > 0 := by
      apply mul_pos 
      linarith 
      positivity
    have h3 : (1 / x) * (2014 : ℝ) ^ x > 0 := by
      apply mul_pos 
      have h4 : (1 / x) > 0 := by
        apply div_pos 
        norm_num 
        all_goals linarith
      linarith
      positivity

    have h5 : (x * (2014 : ℝ) ^ ((1 : ℝ) / x) ) * ( (1 / x) * (2014 : ℝ) ^ x ) = (2014 : ℝ) ^ ((1 / x + x) ) := by
      have h6 : (x * (2014 : ℝ) ^ ((1 : ℝ) / x) ) * ( (1 / x) * (2014 : ℝ) ^ x ) = (x * (1 / x) ) * ( (2014 : ℝ) ^ ((1 : ℝ) / x) * (2014 : ℝ) ^ x ) := by 
        ring
      have h7 : ( (2014 : ℝ) ^ ((1 : ℝ) / x) * (2014 : ℝ) ^ x ) = (2014 : ℝ) ^ ((1 / x + x) ) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals norm_num
      have h8 : x * (1 / x) = 1 := by 
        field_simp
      rw [h6, h7, h8]
      <;> norm_num
    have h6 : (1 / x + x) = (2 : ℝ) := by
      have h7 : (x * (2014 : ℝ) ^ ((1 : ℝ) / x) ) * ( (1 / x) * (2014 : ℝ) ^ x ) ≤ ( ( (x * (2014 : ℝ) ^ ((1 : ℝ) / x) + (1 / x) * (2014 : ℝ) ^ x ) / 2 ) ) ^ 2 := by 
        nlinarith [ sq_nonneg (x * (2014 : ℝ) ^ ((1 : ℝ) / x) - (1 / x) * (2014 : ℝ) ^ x ) ]
      have h8 : ( (x * (2014 : ℝ) ^ ((1 : ℝ) / x) + (1 / x) * (2014 : ℝ) ^ x ) / 2 ) ^ 2 = (2014 ^ 2 : ℝ) := by 
        rw [show x * (2014 : ℝ) ^ ((1 : ℝ) / x) + (1 / x) * (2014 : ℝ) ^ x = (4028 : ℝ) by linarith ] 
        norm_num 
      have h9 : (x * (2014 : ℝ) ^ ((1 : ℝ) / x) ) * ( (1 / x) * (2014 : ℝ) ^ x ) ≤ (2014 ^ 2 : ℝ) := by
        nlinarith [ h7, h8 ]
      have h10 : (2014 : ℝ) ^ ((1 / x + x) ) ≤ (2014 ^ 2 : ℝ) := by 
        nlinarith [ h5, h9 ]
      have h11 : (1 / x + x ) ≤ (2 : ℝ) := by
        by_contra h12 
        push_neg at h12 
        have h14 : (1 / x + x ) > (2 : ℝ) := by 
          nlinarith 
        have h15 : (2014 : ℝ) ^ ((1 / x + x) ) > (2014 ^ 2 : ℝ) := by
          have h151 : (1 / x + x ) > (2 : ℝ) := h14
          have h152 : (2014 : ℝ) ^ ((1 / x + x) ) > (2014 : ℝ) ^ (2 : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt 
            all_goals linarith
          rw [show (2014 : ℝ) ^ (2 : ℝ) = (2014 ^ 2 : ℝ) by norm_num] at h152 
          linarith 
        linarith
      have h14 : (1 / x + x ) ≥ (2 : ℝ) := by
        have : (x ) + (1 / x ) - (2 : ℝ) ≥ 0 := by
          have h14 : x + 1 / x - 2 = (x - 1) ^ 2 / x := by 
            field_simp 
            ring 
          rw [h14]
          have h15 : (x - 1) ^ 2 ≥ 0 := by 
            nlinarith 
          have h16 : (x - 1) ^ 2 / x ≥ 0 := by 
            apply div_nonneg 
            linarith 
            all_goals linarith 
          linarith 
        linarith 
      linarith [ h14, h11 ]
    have h7 : x = 1 := by
      field_simp at h6 
      <;> nlinarith 
    assumption
  · -- Assume x = 1, show it's in the set
    intro h_eq
    rw [h_eq]
    constructor 
    · norm_num 
    · -- verify the equation 
      norm_num