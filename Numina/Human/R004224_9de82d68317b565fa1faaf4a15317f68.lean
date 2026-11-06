import Mathlib

open Real Set

set_option maxHeartbeats 500000

theorem algebra_243558
  (m : ℝ) 
  (h : {x : ℝ | abs ((x - 1) * (x - 3)) = m * x}.encard = 4)
   : m ∈ Ioo 0 (4-2*√3) := by

  have : √3 > 0 := by positivity
  have h_sq3: √3^2=3 := by rw [sq_sqrt (by positivity)]
  have h_sq3a : 2 * √3 ≤ 4 := by nlinarith

  let S := {x : ℝ | abs ((x - 1) * (x - 3)) = m * x}
  have hS : S.encard = 4 := by
    rw [h]

  have h_set0 : m ∈ Iic (-4-2*√3) → S = {2 + m/2 - √(4 + 8*m + m^2)/2, 2 + m/2 + √(4 + 8*m + m^2)/2} := by
    intro hm
    simp at hm
    have hm1 : m < 0 := by linarith
    have hm2 : (m+4)^2 ≥ 12 := by
        have : (m+4)^2 ≥ (-2*√3)^2 := by nlinarith
        ring_nf at this
        rw [h_sq3] at this
        linarith

    ext x
    unfold S
    simp
    constructor
    . intro hx
      have hx1 : x ≤ 0 := by
        by_contra h
        simp at h
        have : abs ((x - 1) * (x - 3)) ≥ 0 := by positivity
        nlinarith

      have hx2 : (x - 1) * (x - 3) ≥ 0 := by
        nlinarith

      rw [abs_of_nonneg hx2] at hx
      
      have : (x-(2 + m/2 - √(4 + 8*m + m^2)/2))*(x-(2 + m/2 + √(4 + 8*m + m^2)/2)) = 0 := by
        ring_nf
        rw [sq_sqrt (by linarith)] 
        ring_nf
        rw [mul_comm x m, ← hx]
        ring_nf

      simp at this
      rcases this with h1 | h2
      . left; linarith
      . right; linarith

    . intro hx
      rcases hx with rfl | rfl
      . ring_nf
        rw [sq_sqrt (by linarith)]
        ring_nf
        rw [abs_of_nonneg]
        suffices (m+4) ≤ √(4 + m * 8 + m ^ 2) by
          nlinarith
        have : √(4 + m * 8 + m ^ 2) ≥ 0 := by positivity
        nlinarith

      . ring_nf
        rw [sq_sqrt (by linarith)]
        ring_nf
        rw [abs_of_nonneg]
        suffices √(4 + m * 8 + m ^ 2) ≤ -(m+4) by
          nlinarith
        rw [sqrt_le_iff]
        constructor
        . linarith
        . nlinarith

  have h_set1 : m ∈ Ioo (-4-2*√3) 0 → S = ∅ := by
    intro ⟨ hm1, hm2 ⟩
    ext x
    unfold S
    simp
    intro hx
    have hx1 : x ≤ 0 := by
      by_contra h
      simp at h
      have : abs ((x - 1) * (x - 3)) ≥ 0 := by positivity
      nlinarith
    
    have hx2: (x - 1) * (x - 3) > 0 := by
      nlinarith

    rw [abs_of_pos hx2] at hx

    by_cases hm3 : (m + 4)^2 < 12
    . have : (x-(m+4)/2)^2 ≥ 0 := by positivity
      nlinarith
    . simp at hm3
      have : (x-(2 + m/2 - √(4 + 8*m + m^2)/2))*(x-(2 + m/2 + √(4 + 8*m + m^2)/2)) = 0 := by
        ring_nf
        rw [sq_sqrt (by linarith)] 
        ring_nf
        rw [mul_comm x m, ← hx]
        ring_nf

      simp at this
      rcases this with h1 | h2
      . have : x = 2 + m/2 - √(4 + 8*m + m^2)/2 := by linarith
        rw [this] at hx1

        have hm4 : 0 ≤ 4 + m := by nlinarith
        have : 4 + m ≤ √(4 + 8 * m + m ^ 2) := by linarith
        rw [le_sqrt hm4 (by linarith)] at this
        ring_nf at this
        linarith

      . have : x = 2 + m/2 + √(4 + 8*m + m^2)/2 := by linarith
        rw [this] at hx1
        have : √(4 + 8 * m + m ^ 2) ≥ 0 := by positivity
        nlinarith

  have h_set2 : m ∈ Icc 0 (4-2*√3) → S = {2 - m/2 - √(4 - 8*m + m^2)/2, 2 - m/2 + √(4 - 8*m + m^2)/2, 2 + m/2 - √(4 + 8*m + m^2)/2, 2 + m/2 + √(4 + 8*m + m^2)/2} := by
    intro ⟨ hm1, hm2 ⟩
    ext x
    unfold S
    simp
    constructor
    . intro hx
      by_cases hx1 : x ∈ Icc 1 3
      . have hx2: (x - 1) * (x - 3) ≤ 0 := by
          have : x ≥ 1 := hx1.1
          have : x ≤ 3 := hx1.2
          nlinarith

        rw [abs_of_nonpos hx2] at hx
        have : (x-2+m/2+√(4-8*m+m^2)/2)*(x-2+m/2-√(4-8*m+m^2)/2) = 0 := by 
          ring_nf
          rw [sq_sqrt (by nlinarith)]
          ring_nf
          rw [mul_comm x m, ← hx]
          ring_nf

        simp at this
        rcases this with h1 | h2
        . have : x = 2 - m/2 - √(4-8*m+m^2)/2 := by linarith
          tauto
        . have : x = 2 - m/2 + √(4-8*m+m^2)/2 := by linarith
          tauto
      . simp at hx1
        have hx2: (x - 1) * (x - 3) > 0 := by
          by_cases h: 1 ≤ x
          . have := hx1 h
            nlinarith
          . nlinarith
        
        rw [abs_of_pos hx2] at hx
        have : (x-2-m/2+√(4+8*m+m^2)/2)*(x-2-m/2-√(4+8*m+m^2)/2) = 0 := by 
          ring_nf
          rw [sq_sqrt (by nlinarith)]
          ring_nf
          rw [mul_comm x m, ← hx]
          ring_nf

        simp at this
        rcases this with h1 | h2
        . have : x = 2 + m/2 - √(4+8*m+m^2)/2 := by linarith
          tauto
        . have : x = 2 + m/2 + √(4+8*m+m^2)/2 := by linarith
          tauto

    . intro hx
      rcases hx with rfl | rfl | rfl | rfl
      . ring_nf
        rw [sq_sqrt (by nlinarith)]
        ring_nf
        rw [abs_of_nonpos]
        linarith
        suffices √(4 - m * 8 + m ^ 2) ≤ 4-m by
          nlinarith

        rw [sqrt_le_iff]
        constructor
        . linarith
        . nlinarith

      . ring_nf
        rw [sq_sqrt (by nlinarith)]
        ring_nf
        rw [abs_of_nonpos]
        linarith
        have : √(4 - m * 8 + m ^ 2) ≥ 0 := by positivity
        nlinarith
        
      . ring_nf
        rw [sq_sqrt (by nlinarith)]
        ring_nf
        rw [abs_of_nonneg]
        suffices √(4 + m * 8 + m ^ 2) ≤ 4 + m by
          nlinarith

        rw [sqrt_le_iff]
        constructor
        . linarith
        . nlinarith
      
      . ring_nf
        rw [sq_sqrt (by nlinarith)]
        ring_nf
        rw [abs_of_nonneg]
        have : √(4 + m * 8 + m ^ 2) ≥ 0 := by positivity
        nlinarith

  have h_set3 : m ∈ Ioi (4-2*√3) → S = {2 + m/2 - √(4 + 8*m + m^2)/2, 2 + m/2 + √(4 + 8*m + m^2)/2} := by
    intro hm
    simp at hm
    unfold S
    ext x
    simp
    constructor
    . intro hx
      by_cases hx1 : x ∈ Icc 1 3
      . have hx2: (x - 1) * (x - 3) ≤ 0 := by
          have : x ≥ 1 := hx1.1
          have : x ≤ 3 := hx1.2
          nlinarith

        rw [abs_of_nonpos hx2] at hx
        by_cases hm1 : (m-4)^2 < 12
        . have : (x-2+m/2)^2 ≥ 0 := by positivity
          nlinarith
        . simp at hm1
          have : (x-2+m/2+√(4-8*m+m^2)/2)*(x-2+m/2-√(4-8*m+m^2)/2) = 0 := by 
            ring_nf
            rw [sq_sqrt (by linarith)]
            ring_nf
            rw [mul_comm x m, ← hx]
            ring_nf

          simp at this
          rcases this with h1 | h2
          . have : x = 2 - m/2 - √(4-8*m+m^2)/2 := by linarith
            have : 2 - m/2 - √(4-8*m+m^2)/2 < 0 := by
              have : √(4-8*m+m^2) ≥ 0 := by positivity
              nlinarith
            nlinarith

          . have : x = 2 - m/2 + √(4-8*m+m^2)/2 := by linarith
            have : 2 - m/2 + √(4-8*m+m^2)/2 < 0 := by
              suffices √(4-8*m+m^2) < m-4 by linarith
              rw [sqrt_lt]
              all_goals nlinarith

            nlinarith

      . simp at hx1
        have hx2 : (x - 1) * (x - 3) > 0 := by
          by_cases h: 1 ≤ x
          . have := hx1 h
            nlinarith
          . nlinarith

        rw [abs_of_pos hx2] at hx
        have : (x-2-m/2+√(4+8*m+m^2)/2)*(x-2-m/2-√(4+8*m+m^2)/2) = 0 := by 
          ring_nf
          rw [sq_sqrt (by nlinarith)]
          ring_nf
          rw [mul_comm x m, ← hx]
          ring_nf

        simp at this
        rcases this with h1 | h2
        . left; linarith
        . right; linarith

    . intro hx
      rcases hx with rfl | rfl
      . ring_nf
        rw [sq_sqrt (by nlinarith)]
        ring_nf
        rw [abs_of_pos]
        suffices √(4 + m * 8 + m ^ 2) < m + 4 by
          nlinarith
        rw [sqrt_lt]
        all_goals nlinarith

      . ring_nf
        rw [sq_sqrt (by nlinarith)]
        ring_nf
        rw [abs_of_pos]
        have : √(4 + m * 8 + m ^ 2) ≥ 0 := by positivity
        nlinarith

  by_cases hm0 : m ≤ -4-2*√3
  . have := h_set0 hm0
    rw [this] at hS
    by_cases h : 2 + m / 2 - √(4 + 8 * m + m ^ 2) / 2 = 2 + m / 2 + √(4 + 8 * m + m ^ 2) / 2
    . rw [h] at hS
      simp at hS
    . rw [Set.encard_pair h] at hS
      norm_num at hS

  . simp at hm0
    rcases lt_trichotomy m 0 with hm | rfl | hm1
    . have := h_set1 ⟨ hm0, hm ⟩
      rw [this] at hS
      simp at hS
    . simp at h_set2
      have h4: √4=2 := by rw [(by ring: (4:ℝ)=2^2), sqrt_sq (by norm_num)]
      
      have := h_set2 h_sq3a
      rw [this] at hS
      rw [h4] at hS
      rw [Set.encard_pair] at hS
      simp at hS
      by_contra h
      ring_nf at h
      norm_num at h

    . rcases lt_trichotomy m (4-2*√3) with hm2 | rfl | hm
      . tauto
      . simp at h_set2
        have := h_set2 h_sq3a
        rw [this] at hS
        ring_nf at hS
        rw [sq_sqrt (by linarith)] at hS

        ring_nf at hS
        simp at hS
        repeat rw [Set.encard_insert_of_not_mem] at hS
        simp at hS
        norm_num at hS
        . by_contra h
          simp at h
          rcases h with h1 | h2
          . field_simp at h1
            norm_num at h1
          . rw [sqrt_eq_zero'] at h2
            linarith
        . by_contra h
          rcases h with h1 | h2
          . field_simp at h1
            have : √(64 - √3 * 32) = 8 - √3 * 4 := by linarith
            rw [sqrt_eq_iff_mul_self_eq_of_pos (by linarith)] at this
            ring_nf at this
            rw [h_sq3] at this
            nlinarith
       
          . simp at h2
            have : √(64 - √3 * 32) ≥ 0 := by positivity
            linarith

      . have := h_set3 hm
        rw [this] at hS
        by_cases h : 2 + m / 2 - √(4 + 8 * m + m ^ 2) / 2 = 2 + m / 2 + √(4 + 8 * m + m ^ 2) / 2
        . rw [h] at hS
          simp at hS
        . rw [Set.encard_pair h] at hS
          norm_num at hS
