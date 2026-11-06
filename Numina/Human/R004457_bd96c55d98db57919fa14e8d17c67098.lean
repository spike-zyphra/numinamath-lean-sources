import Mathlib

open Real

/- 6. If the equation $|x-a|=\left|\frac{4}{x}\right|$ with respect to $x$ has exactly 3 different real roots, then the sum of the squares of these 3 roots is -/
theorem algebra_269448 (a : ℝ) (h : {x | x ≠ 0 ∧ abs (x - a) = abs (4 / x)}.encard = 3) :
  ∃ x1 x2 x3 : ℝ, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧
    abs (x1 - a) = abs (4 / x1) ∧
    abs (x2 - a) = abs (4 / x2) ∧
    abs (x3 - a) = abs (4 / x3) ∧
    x1^2 + x2^2 + x3^2 = 28 := by

  have h_set1 : a^2 < 16 → {x | x ≠ 0 ∧ abs (x - a) = abs (4 / x)} = {a/2 - sqrt (16 + a^2)/2, a/2 + sqrt (16 + a^2)/2} := by
    intro ha
    ext x
    simp
    constructor
    . intro ⟨ hx1, hx2 ⟩
      rw [abs_div] at hx2
      field_simp at hx2
      rw [← abs_mul] at hx2
      rw [abs_eq (by positivity)] at hx2
      rcases hx2 with hx2 | hx2
      . have : x^2=a*x+4 := by linarith
        have : (x-(a/2 - sqrt (16 + a^2)/2))* (x-(a/2 + sqrt (16 + a^2)/2)) = 0 := by
          ring_nf
          rw [sq_sqrt (by positivity)]
          rw [this]
          linarith

        simp at this
        rcases this with h1 | h2
        . left; linarith
        . right; linarith

      . have : x^2=a*x-4 := by linarith
        have h1: (x-a/2)^2=a^2/4-4 := by
          ring_nf
          rw [this]
          ring_nf
        have : (x-a/2)^2 ≥ 0 := by positivity
        nlinarith

    . intro hx
      suffices x ≠ 0 ∧ (x ≠ 0 → abs (x - a) = abs (4 / x)) by tauto
      have h_tauto: (x ≠ 0 → |(x - a) * x| = 4) → (x ≠ 0 → |x - a| = |4 / x|)  := by
        intro h1 h2
        have h3:= h1 h2
        rw [abs_div]
        field_simp
        rw [← abs_mul]
        exact h3

      suffices x ≠ 0 ∧ |(x - a) * x| = 4 by
        constructor
        . exact this.1
        . intro h1
          have h2 : (x ≠ 0 → |(x - a) * x| = 4) := by
            intro hx1
            exact this.2
          exact h_tauto h2 h1

      rcases hx with rfl | rfl
      . constructor
        . by_contra
          have : √(16 + a ^ 2) = a := by linarith
          by_cases ha1 : a ≥ 0
          . rw [sqrt_eq_iff_mul_self_eq (by positivity) ha1] at this
            linarith
          . have : √(16 + a ^ 2) ≥ 0 := by positivity
            linarith
        . ring_nf
          rw [sq_sqrt (by positivity)]
          ring_nf
          norm_num

      . constructor
        . by_contra
          have : √(16 + a ^ 2) = -a := by linarith
          by_cases ha1 : a ≤ 0
          . rw [sqrt_eq_iff_mul_self_eq (by positivity) (by linarith)] at this
            linarith
          . have : √(16 + a ^ 2) ≥ 0 := by positivity
            linarith
        . ring_nf
          rw [sq_sqrt (by positivity)]
          ring_nf
          norm_num

  have h_set2 : a^2 ≥ 16 → {x | x ≠ 0 ∧ abs (x - a) = abs (4 / x)} = {a/2 - sqrt (a^2-16)/2, a/2 + sqrt (a^2-16)/2, a/2 - sqrt (a^2+16)/2, a/2 + sqrt (a^2+16)/2} := by
    intro ha
    ext x
    simp
    constructor
    . intro ⟨ hx1, hx2 ⟩
      rw [abs_div] at hx2
      field_simp at hx2
      rw [← abs_mul] at hx2
      rw [abs_eq (by positivity)] at hx2
      rcases hx2 with hx2 | hx2
      . have : x^2=a*x+4 := by linarith
        have : (x-(a/2 - sqrt (a^2+16)/2))* (x-(a/2 + sqrt (a^2+16)/2)) = 0 := by
          ring_nf
          rw [sq_sqrt (by positivity)]
          rw [this]
          linarith
        simp at this
        rcases this with h1 | h2
        . right; right; left; linarith
        . right; right; right; linarith

      . have : x^2=a*x-4 := by linarith
        have : (x-(a/2 - sqrt (a^2-16)/2))* (x-(a/2 + sqrt (a^2-16)/2)) = 0 := by
          ring_nf
          rw [sq_sqrt (by linarith)]
          rw [this]
          linarith
        simp at this
        rcases this with h1 | h2
        . left; linarith
        . right; left; linarith

    . intro hx
      suffices ¬x = 0 ∧ |(x - a)*x| = 4 by
        obtain ⟨ h1, h2 ⟩ := this
        constructor
        . exact h1
        . rw [abs_div]
          field_simp
          rw [← abs_mul]
          rw [h2]




      rcases hx with rfl | rfl | rfl | rfl
      . constructor
        . by_contra
          have : √(a ^ 2 - 16) = a := by linarith
          by_cases ha1 : a ≥ 0
          . rw [sqrt_eq_iff_mul_self_eq (by linarith) ha1] at this
            linarith
          . have : √(a ^ 2 - 16) ≥ 0 := by positivity
            linarith

        . ring_nf
          rw [sq_sqrt (by linarith)]
          ring_nf
          norm_num
      . constructor
        . by_contra
          have : √(a ^ 2 - 16) = -a := by linarith
          by_cases ha1 : a ≤ 0
          . rw [sqrt_eq_iff_mul_self_eq (by linarith) (by linarith)] at this
            linarith
          . have : √(a ^ 2 - 16) ≥ 0 := by positivity
            linarith

        . ring_nf
          rw [sq_sqrt (by linarith)]
          ring_nf
          norm_num
      . constructor
        . by_contra
          have : √(a ^ 2 + 16) = a := by linarith
          by_cases ha1 : a ≥ 0
          . rw [sqrt_eq_iff_mul_self_eq (by linarith) ha1] at this
            linarith
          . have : √(a ^ 2 + 16) ≥ 0 := by positivity
            linarith
        . ring_nf
          rw [sq_sqrt (by linarith)]
          ring_nf
          norm_num
      . constructor
        . by_contra
          have : √(a ^ 2 + 16) = -a := by linarith
          by_cases ha1 : a ≤ 0
          . rw [sqrt_eq_iff_mul_self_eq (by linarith) (by linarith)] at this
            linarith
          . have : √(a ^ 2 + 16) ≥ 0 := by positivity
            linarith
        . ring_nf
          rw [sq_sqrt (by linarith)]
          ring_nf
          norm_num

  have hcard2 : a^2 < 16 → {x | x ≠ 0 ∧ abs (x - a) = abs (4 / x)}.encard = 2 := by
    intro ha
    have := h_set1 ha
    rw [this] at h
    rw [Set.encard_pair] at h
    tauto
    . by_contra h_contra
      -- have : -√(16 + a ^ 2) = √(16 + a ^ 2) := by nlinarith
      have : √(16 + a ^ 2) = 0 := by nlinarith
      rw [sqrt_eq_zero (by positivity)] at this
      nlinarith

  have hcard3 : a^2=16 → {x | x ≠ 0 ∧ abs (x - a) = abs (4 / x)}.encard = 3 := by
    intro ha
    rw [ha] at h_set2
    simp at h_set2
    rw [h_set2]
    repeat rw [Set.encard_insert_of_not_mem]
    all_goals simp; norm_num
    . by_contra
      have : √32 = 0 := by linarith
      rw [sqrt_eq_zero (by norm_num)] at this
      norm_cast at this
    . by_contra
      have : √32 = 0 := by linarith
      rw [sqrt_eq_zero (by norm_num)] at this
      norm_cast at this

  have hcard4 : a^2>16 → {x | x ≠ 0 ∧ abs (x - a) = abs (4 / x)}.encard = 4 := by
    intro ha
    have : a^2 ≥ 16 := by linarith
    have := h_set2 this
    rw [this]
    repeat rw [Set.encard_insert_of_not_mem]
    all_goals simp; norm_num
    . by_contra
      have : √(a ^ 2 + 16) = 0 := by linarith
      rw [sqrt_eq_zero (by positivity)] at this
      linarith
    . constructor
      . by_contra
        have h1: √(a ^ 2 + 16) = -√(a ^ 2 - 16) := by linarith
        have : √(a ^ 2 + 16) ≥ 0 := by positivity
        rw [h1] at this
        have : √(a ^ 2 - 16) ≥ 0 := by positivity
        have : √(a ^ 2 - 16) = 0 := by linarith
        rw [sqrt_eq_zero (by linarith)] at this
        linarith

      . by_contra
        have :  √(a ^ 2 + 16) = √(a ^ 2 - 16) := by linarith
        rw [sqrt_inj (by linarith) (by linarith)] at this
        linarith

    . constructor
      . by_contra
        have : √(a ^ 2 - 16) = 0 := by linarith
        rw [sqrt_eq_zero (by linarith)] at this
        linarith
      . constructor
        . by_contra
          have : √(a ^ 2 - 16) = √(a ^ 2 + 16) := by linarith
          rw [sqrt_inj (by linarith) (by linarith)] at this
          linarith
        . by_contra
          have h1: √(a ^ 2 - 16) = -√(a ^ 2 + 16) := by linarith
          have : √(a ^ 2 - 16) ≥ 0 := by positivity
          rw [h1] at this
          have : √(a ^ 2 + 16) ≥ 0 := by positivity
          have : √(a ^ 2 + 16) = 0 := by linarith
          rw [sqrt_eq_zero (by linarith)] at this
          linarith

  have ha1 : a^2 = 16 := by
    rcases lt_trichotomy (a^2) 16 with h1 | h2 | h3
    . have := hcard2 h1
      rw [h] at this
      tauto
    . assumption
    . have := hcard4 h3
      rw [h] at this
      tauto

  have ha2 : a = 4 ∨ a = -4 := by
    have : (a-4)*(a+4) = 0 := by linarith
    simp at this
    rcases this with h1 | h2
    . left; linarith
    . right; linarith

  use a/2, a/2-2*√2, a/2+2*√2
  constructor
  . by_contra
    have : √2 = 0 := by linarith
    rw [sqrt_eq_zero (by norm_num)] at this
    linarith

  . constructor
    . by_contra
      have : √2 = 0 := by linarith
      rw [sqrt_eq_zero (by norm_num)] at this
      linarith
    . constructor
      . by_contra
        have : √2 = 0 := by linarith
        rw [sqrt_eq_zero (by norm_num)] at this
        linarith
      . constructor
        . by_contra h_contra
          rcases ha2 with rfl | rfl
          norm_num at h_contra
          ring_nf at h_contra
          norm_num at h_contra

        . constructor
          . rcases ha2 with rfl | rfl
            . rw [abs_div]
              ring_nf
              have : |2 - √2 * 2| ≠ 0 := by
                by_contra h_contra
                simp at h_contra
                have : √2 = 1 := by linarith
                rw [sqrt_eq_iff_mul_self_eq_of_pos (by positivity)] at this
                norm_num at this

              field_simp
              rw [← abs_mul]
              ring_nf
              rw [sq_sqrt (by positivity)]
              norm_num

            . rw [abs_div]
              ring_nf
              have : |-2 - √2 * 2| ≠ 0 := by
                by_contra h_contra
                simp at h_contra
                have : √2 ≥ 0 := by positivity
                linarith

              field_simp
              rw [← abs_mul]
              ring_nf
              rw [sq_sqrt (by positivity)]
              norm_num

          . constructor
            . rcases ha2 with rfl | rfl
              . rw [abs_div]
                have : |2 + √2 * 2| ≠ 0 := by positivity
                field_simp
                rw [← abs_mul]
                ring_nf
                rw [sq_sqrt (by positivity)]
                norm_num
              . rw [abs_div]
                ring_nf
                have : |-2 + √2 * 2| ≠ 0 := by
                  by_contra h_contra
                  simp at h_contra
                  have : √2 = 1 := by linarith
                  rw [sqrt_eq_iff_mul_self_eq_of_pos (by positivity)] at this
                  norm_num at this

                field_simp
                rw [← abs_mul]
                ring_nf
                rw [sq_sqrt (by positivity)]
                norm_num

            . ring_nf
              rw [ha1]
              rw [sq_sqrt (by norm_num)]
              norm_num
