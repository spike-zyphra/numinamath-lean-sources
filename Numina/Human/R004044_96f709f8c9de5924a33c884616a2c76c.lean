import Mathlib

open Real Set
set_option maxHeartbeats 500000

/- 2. Find all values of the parameter $a$, for each of which the equation $\left|x^{3}-a^{3}\right|=x-a$ has three distinct roots. -/
theorem algebra_233022 (a : ℝ) :
  {x | |x^3 - a^3| = x - a}.encard = 3
   ↔ a ∈ Ioo (-(2 / √3)) (-(1 / √3))  := by

  have hf1 : StrictMono (fun x:ℝ => x^3) := by
    intro x y hxy
    have : x ^ 2 + x * y + y ^ 2 > 0 := by
      nlinarith [sq_nonneg (x + y)]
    simp
    nlinarith [sq_nonneg (x + y)]
  
  have : 0 < 2 / √3 := by positivity

  let S := {x| |x^3 - a^3| = x- a}

  have h_set1 : a < -(2 / √3) ∨ a > 1 / √3 → S = {a} := by
    intro ha

    ext x; simp; unfold S
    constructor
    . intro hx
      simp at hx
      rcases lt_trichotomy x a with h | h | h
      . have : x ^ 3 - a ^ 3 < 0 := by
          have := hf1 h
          simp at this
          linarith
        rw [abs_of_neg this] at hx
        have : (x-a)*(x^2 + a*x + a^2+1) = 0 := by
          linarith
        simp at this
        rcases this with h | h
        . linarith
        . have : (x+a/2)^2≥ 0 := by positivity
          have : 4/3 < a^2 := by
            rw [(by ring_nf; field_simp : 4/3=(2/√3)^2)]
            rw [sq_lt_sq]
            rcases ha with h | h
            . rw [abs_of_pos (by linarith)]
              rw [abs_of_pos (by linarith)]
              linarith
            . rw [abs_of_pos (by linarith)]
              rw [abs_of_neg (by linarith)]
              linarith
          nlinarith

      . exact h
      . have : x ^ 3 - a ^ 3 > 0 := by
          have := hf1 h
          simp at this
          linarith

        rw [abs_of_pos this] at hx
        have : (x-a)*(x^2 + a*x + a^2-1) = 0 := by
          linarith
        simp at this
        rcases this with h | h
        . linarith
        . by_cases ha1 : a < -(2 / √3) ∨ a > 2 / √3
          . have : (x+a/2)^2≥ 0 := by positivity
            have : 4/3 < a^2 := by
              rw [(by ring_nf; field_simp : 4/3=(2/√3)^2)]
              rw [sq_lt_sq]
              rw [abs_of_pos (by linarith)]
              rcases ha1 with h | h
              . have : (2 / √3) > 0 := by positivity
                rw [abs_of_neg (by linarith)]
                linarith
              . rw [abs_of_pos (by linarith)]
                linarith
            nlinarith
          . simp at ha1
            have : 1 / √3 > 0 := by positivity
            have ha2 : a > 1 / √3 := by
              rcases ha with h | h
              . linarith
              . linarith

            have ha3 : 1/3 < a ^ 2 := by
              rw [(by ring_nf; field_simp : 1/3=(1/√3)^2)]
              rw [sq_lt_sq]
              nth_rw 1 [abs_of_pos (by positivity)]
              rw [abs_of_pos (by linarith)]
              linarith

            have ha4 : a ^ 2 ≤ 4/3 := by
              rw [(by ring_nf; field_simp : 4/3=(2/√3)^2)]
              rw [sq_le_sq]
              nth_rw 2 [abs_of_pos (by positivity)]
              rw [abs_of_pos (by linarith)]
              linarith

            have : (x-(-a/2 - √(4 - 3*a^2)/2))*(x-(-a/2 + √(4 - 3*a^2)/2)) = 0 := by
              ring_nf
              rw [sq_sqrt (by linarith), ← h]
              ring_nf
            simp at this
            rcases this with h | h
            . have : x = (-a/2 - √(4 - 3*a^2)/2) := by linarith
              subst x
              have : √(4 - 3*a^2) <  -3*a  := by linarith
              have : √(4 - 3*a^2) ≥ 0 := by positivity
              linarith
            . have : x = (-a/2 + √(4 - 3*a^2)/2) := by linarith
              subst x
              have : 3*a < √(4 - 3*a^2) := by linarith
              rw [lt_sqrt (by linarith)] at this
              linarith

    . intro hx
      subst x
      simp


  have h_set2 : a ∈ Ico (-(2 / √3)) (-(1 / √3)) → S = {a,-a/2 - √(4 - 3*a^2)/2, -a/2 + √(4 - 3*a^2)/2} := by
    intro ha

    have : a^2 ≤ 4/3 := by
      simp at ha
      have : (√3)⁻¹ > 0 := by positivity
      
      rw [(by ring_nf; field_simp : 4/3=(2/√3)^2)]
      rw [sq_le_sq]
      nth_rw 2 [abs_of_pos (by positivity)]
      rw [abs_of_neg (by linarith)]
      linarith

    have ha1 : 0 ≤ 4 - a ^ 2 * 3 := by linarith
    have ha2 : 1/3 < a^2 := by
      simp at ha
      have : (√3)⁻¹ > 0 := by positivity
      rw [(by ring_nf; field_simp : 1/3=(1/√3)^2)]
      rw [sq_lt_sq]
      nth_rw 1 [abs_of_pos (by positivity)]
      rw [abs_of_neg (by linarith)]
      simp
      linarith


    ext x; simp; unfold S
    constructor
    . intro hx
      simp at hx
      rcases lt_trichotomy x a with h | h | h
      . have : x ^ 3 - a ^ 3 < 0 := by
          have := hf1 h
          simp at this
          linarith
        rw [abs_of_neg this] at hx
        have : (x-a)*(x^2 + a*x + a^2+1) = 0 := by
          linarith
        simp at this
        rcases this with h | h
        . linarith
        . have : (x+a/2)^2≥ 0 := by positivity
          linarith
      . left; exact h
      . right
        have : x ^ 3 - a ^ 3 > 0 := by
          have := hf1 h
          simp at this
          linarith
        rw [abs_of_pos this] at hx
        have : (x-a)*(x^2 + a*x + a^2-1) = 0 := by
          linarith
        simp at this
        rcases this with h | h
        . linarith
        . have : (x-(-a/2 - √(4 - 3*a^2)/2))*(x-(-a/2 + √(4 - 3*a^2)/2)) = 0 := by
            ring_nf
            rw [sq_sqrt ha1, ← h]
            ring_nf
            
          simp at this
          rcases this with h | h
          . left; linarith
          . right; linarith

    . intro hx
      have ha2: √(4 - a ^ 2 * 3) ^ 3 = √(4 - a ^ 2 * 3) * (4 - a ^ 2 * 3):= by
        rw [(by norm_num : 3=1+2)]
        rw [pow_add]
        rw [sq_sqrt (by linarith)]
        ring_nf

      have ha3: a * (-3 / 2) + √(4 - a ^ 2 * 3) * (-1 / 2) ≥ 0 := by
        suffices √(4 - a ^ 2 * 3) ≤ -3*a by linarith
        simp at ha
        have : (√3)⁻¹ > 0 := by positivity
        rw [sqrt_le_left (by linarith)]
        linarith  

      have ha4: a * (-3 / 2) + √(4 - a ^ 2 * 3) * (1 / 2) ≥ 0 := by
        have : √(4 - a ^ 2 * 3) ≥ 0 := by positivity
        linarith

      rcases hx with h | h | h
      all_goals subst x; simp
      all_goals ring_nf; rw [ha2, sq_sqrt ha1]; ring_nf  
      . rw [abs_of_nonneg ha3]
      . rw [abs_of_nonneg ha4]
      
      

  have h_set3 : a ∈ Icc (-(1 / √3)) (1 / √3) → S = {a, -a/2 + √(4 - 3*a^2)/2} := by
    intro ha

    have ha1 : a^2 ≤ 1/3 := by
      simp at ha
      field_simp at ha
      rw [(by ring_nf; field_simp : 1/3=(1/√3)^2)]
      rw [sq_le_sq]
      nth_rw 2 [abs_of_pos (by positivity)]
      by_cases h1 : a ≤ 0
      . rw [abs_of_nonpos (by linarith)]
        have := ha.1
        ring_nf at this
        ring_nf
        linarith
      . rw [abs_of_pos (by linarith)]
        linarith

    ext x; simp; unfold S
    constructor
    . intro hx
      simp at hx
      rcases lt_trichotomy x a with h | h | h
      . have : x ^ 3 - a ^ 3 < 0 := by
          have := hf1 h
          simp at this
          linarith
        rw [abs_of_neg this] at hx
        have : (x-a)*(x^2 + a*x + a^2+1) = 0 := by
          linarith
        simp at this
        rcases this with h | h
        . linarith
        . have : (x-a/2)^2≥ 0 := by positivity
          linarith
      . left; exact h
      . right
        have : x ^ 3 - a ^ 3 > 0 := by
          have := hf1 h
          simp at this
          linarith
        rw [abs_of_pos this] at hx
        have : (x-a)*(x^2 + a*x + a^2-1) = 0 := by
          linarith
        simp at this
        rcases this with h | h
        . linarith
        . have : (x-(-a/2 + √(4 - 3*a^2)/2))*(x-(-a/2 - √(4 - 3*a^2)/2)) = 0 := by
            ring_nf
            rw [sq_sqrt (by linarith), ← h]
            ring_nf

          simp at this
          rcases this with h | h
          . linarith
          . have : x = (-a / 2 - √(4 - 3 * a ^ 2) / 2) := by linarith
            subst x
            have : √(4 - 3 * a ^ 2) <  -3*a  := by linarith
            by_cases h1 : a ≤ 0
            . rw [sqrt_lt (by linarith) (by linarith)] at this
              linarith
            . simp at h1
              have : √(4 - 3 * a ^ 2) ≥ 0 := by positivity
              linarith


    . intro hx
      simp
      rcases hx with rfl | rfl
      . ring_nf; norm_num
      . ring_nf
        rw [sq_sqrt (by linarith)]
        have : √(4 - a ^ 2 * 3) ^ 3 = √(4 - a ^ 2 * 3) * (4 - a ^ 2 * 3):= by
          rw [(by norm_num : 3=1+2)]
          rw [pow_add]
          rw [sq_sqrt (by linarith)]
          ring_nf
        rw [this]
        ring_nf
        have : a * (-3 / 2) + √(4 - a ^ 2 * 3) * (1 / 2) ≥ 0 := by
          suffices 3*a ≤ √(4 - a ^ 2 * 3) by linarith
          apply le_sqrt_of_sq_le
          ring_nf
          linarith

        rw [abs_of_nonneg this]
      

  constructor
  . intro hx
    have : √3 > 0 := by positivity
    rcases lt_trichotomy a (-(2 / √3)) with h1 | h1 | h1
    . have : a < -(2 / √3) ∨ a > 1 / √3 := by tauto
      have := h_set1 this
      unfold S at this
      rw [this] at hx
      norm_num at hx

    . have : a ∈ Ico (-(2 / √3)) (-(1 / √3)) := by
        simp; subst a
        norm_num
        have : (√3)⁻¹ > 0 := by positivity
        ring_nf
        linarith

      have := h_set2 this
      have : S.encard = 2 := by
        rw [this]
        have : √(4 - 3 * a ^ 2) / 2 = 0 := by
          rw [h1]
          ring_nf
          simp
          norm_num

        rw [this]
        simp
        rw [Set.encard_pair]
        by_contra h
        have : a = 0 := by linarith
        have : (2 / √3) > 0 := by positivity
        linarith

      unfold S at this
      rw [this] at hx
      norm_num at hx

    . by_cases h2 : a < -(1 / √3)
      . tauto
      . simp at h2
        by_cases h3 : a ≤ (1 / √3)

        . simp at h3
          have : a ∈ Icc (-(1 / √3)) (1 / √3) := by simp; tauto
          have := h_set3 this
          unfold S at this
          rw [this] at hx
          by_cases h : a = -a / 2 + √(4 - 3 * a ^ 2) / 2
          . rw [← h] at hx
            have : {a,a}= ({a}:Set ℝ) := by simp
            rw [this] at hx
            norm_num at hx

          . rw [Set.encard_pair h] at hx
            norm_num at hx
        . field_simp at h3
          have : a < -(2 / √3) ∨ a > 1 / √3 := by tauto
          have := h_set1 this
          unfold S at this
          rw [this] at hx
          norm_num at hx

  . intro ha
    have ha1: a ∈ Ico (-(2 / √3)) (-(1 / √3)) := by
      simp at ha ⊢
      have ⟨ h1, h2 ⟩ := ha
      have :  -(2 / √3) ≤ a := by linarith
      tauto
    have := h_set2 ha1
    unfold S at this
    rw [this]

    have : a^2 < 4/3 := by
      simp at ha
      have : (√3)⁻¹ > 0 := by positivity
      rw [(by ring_nf; field_simp : 4/3=(2/√3)^2)]
      rw [sq_lt_sq]
      nth_rw 2 [abs_of_pos (by positivity)]
      rw [abs_of_neg (by linarith)]
      linarith
    repeat rw [Set.encard_insert_of_not_mem]
    all_goals simp; norm_num
    all_goals by_contra h
    . have : √(4 - 3 * a ^ 2) = 0 := by linarith
      rw [sqrt_eq_zero (by linarith)] at this
      have : (a-2/√3)*(a+2/√3) = 0 := by
        ring_nf
        field_simp
        linarith
      simp at this
      rcases this with h | h
      . have : a = 2 / √3 := by linarith
        subst a
        simp at ha
        have : (√3)⁻¹ > 0 := by positivity
        linarith

        
      . have : a = -(2 / √3) := by linarith
        subst a
        simp at ha
        
      

    . simp at h ha1
      have : (√3)⁻¹ > 0 := by positivity

      have : ¬a = -a / 2 - √(4 - 3 * a ^ 2) / 2 := by
        by_contra h
        have : √(4 - 3 * a ^ 2) = -3*a := by linarith
        rw [sqrt_eq_iff_eq_sq (by linarith) (by linarith)] at this
        have : a^2 = 1/3 := by linarith
        have : (a-1/√3)*(a+1/√3) = 0 := by
          ring_nf
          field_simp
          linarith
        simp at this
        rcases this with h | h
        . have : a = (√3)⁻¹ := by linarith
          subst a
          simp at ha
          have : (√3) > 0 := by positivity
          linarith
        . have : a = -(√3)⁻¹ := by linarith
          subst a
          simp at ha
          
      have := h this
      have : √(4 - 3 * a ^ 2) = 3*a := by linarith
      have : √(4 - 3 * a ^ 2) ≥ 0 := by positivity
      linarith
