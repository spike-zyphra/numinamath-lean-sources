import Mathlib

set_option maxHeartbeats 1000000

theorem algebra_175364
  {f g: ℝ → ℝ} {a b : ℝ}
  (hf : f = fun x => x^2 + x - 2)
  (hg : g = fun x => (abs (f x) - f x) / 2)
  (ha : a > 0):
  (∀ x, g x = if x ∈ Set.Ioo (-2) 1 then -x^2 - x + 2 else 0) ∧
  ({x | g x = a * x + b}.encard = 3 ↔
  (a < 3 ∧ b ∈ Set.Ioo (2*a) ((a^2+2*a+9)/4))) := by

  have hgx : ∀ x, g x = if x ∈ Set.Ioo (-2) 1 then -x^2 - x + 2 else 0 := by
    intro x
    rw [hg]
    simp
    split_ifs with h1
    . have : f x < 0 := by
        rw [hf]
        simp
        nlinarith [sq_nonneg (x+1/2)]
      rw [abs_of_neg this, hf]
      ring
    . have : 0 ≤ f x := by
        rw [hf]
        simp
        simp at h1
        by_cases h2 : -2 < x
        . have := h1 h2
          nlinarith [sq_nonneg (x+1/2)]
        . nlinarith [sq_nonneg (x+1/2)]
      rw [abs_of_nonneg this, hf]
      ring

  have ha1 : 2 * a ≤ (a^2+2*a+9)/4 := by
    nlinarith [sq_nonneg (a-3)]

  let S := {x | g x = a * x + b}
  let x0 := -b/a
  have hset1 : b < -a → S = {x0} := by
    intro h
    ext x
    unfold S
    simp
    constructor
    . intro hx
      rw [hgx x] at hx
      split_ifs at hx with h1
      . let x1 := -1/2 - a/2 - √(a^2+2*a+9-4*b)/2
        let x2 := -1/2 - a/2 + √(a^2+2*a+9-4*b)/2
        have : (x-x1) * (x-x2) = 0 := by
          ring_nf
          rw [show x^2 = 2-x-a*x-b by linarith]
          rw [Real.sq_sqrt (by linarith)]
          ring_nf

        simp at this
        rcases this with h | h
        . have : x = x1 := by linarith
          rw [this] at h1
          have := h1.1
          unfold x1 at this
          have : √(a ^ 2 + 2 * a + 9 - 4 * b) < 3 - a := by linarith
          by_cases h : 0 < 3 - a
          . rw [Real.sqrt_lt' h] at this
            linarith
          . have : √(a ^ 2 + 2 * a + 9 - 4 * b) ≥ 0 := by positivity
            linarith
        . have : x = x2 := by linarith
          rw [this] at h1
          have := h1.2
          unfold x2 at this
          have : √(a ^ 2 + 2 * a + 9 - 4 * b) < 3 + a := by linarith
          rw [Real.sqrt_lt' (by linarith)] at this
          linarith

      . unfold x0
        field_simp
        linarith
    . intro hx
      rw [hgx x, hx]
      unfold x0
      split_ifs with h1
      . simp at h1
        have := h1.2
        rw [div_lt_iff₀ ha] at this
        linarith
      . field_simp
        linarith

  have hset2 : b ∈ Set.Ico (-a) (2*a) → S = {-1/2 - a/2 + √(a^2+2*a+9-4*b)/2} := by
    intro ⟨h1, h2⟩
    let x0 := -b/a
    let x1 := -1/2 - a/2 - √(a^2+2*a+9-4*b)/2
    let x2 := -1/2 - a/2 + √(a^2+2*a+9-4*b)/2

    suffices S = {x2} by 
      unfold x2 at this
      exact this

    ext x
    unfold S
    simp
    constructor
    . intro hx
      rw [hgx x] at hx
      split_ifs at hx with h1
      . have : (x-x1) * (x-x2) = 0 := by
          ring_nf
          rw [show x^2 = 2-x-a*x-b by linarith]
          rw [Real.sq_sqrt (by linarith)]
          ring_nf

        simp at this
        rcases this with h | h
        . have : x = x1 := by linarith
          rw [this] at h1
          have := h1.1
          unfold x1 at this
          have : √(a ^ 2 + 2 * a + 9 - 4 * b) < 3 - a := by linarith
          by_cases h : 0 < 3 - a
          . rw [Real.sqrt_lt' h] at this
            linarith
          . have : √(a ^ 2 + 2 * a + 9 - 4 * b) ≥ 0 := by positivity
            linarith
        . linarith

      . have : x = x0 := by
          unfold x0
          field_simp
          linarith
        contrapose h1
        simp
        rw [this]
        rw [this] at h1
        constructor
        . unfold x0
          rw [lt_div_iff₀ ha]
          linarith
        . unfold x0
          rw [div_lt_iff₀ ha]
          by_contra
          have : b=-a := by nlinarith
          contrapose h1
          unfold x0 x2
          simp
          rw [this]
          field_simp
          ring_nf
          rw [show (9 + a * 6 + a ^ 2) = (a+3)^2 by linarith]
          rw [Real.sqrt_sq (by linarith)]
          ring_nf

    . rintro rfl
      rw [hgx x2]
      split_ifs with h1
      . unfold x2
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        ring_nf
      . contrapose h1
        simp
        unfold x2
        constructor
        . suffices a - 3 < √(a ^ 2 + 2 * a + 9 - 4 * b) by linarith
          by_cases h : 0 ≤ a - 3
          . rw [Real.lt_sqrt h]
            linarith
          . have : √(a ^ 2 + 2 * a + 9 - 4 * b) ≥ 0 := by positivity
            linarith
        . suffices √(a ^ 2 + 2 * a + 9 - 4 * b) < 3 + a by linarith
          rw [Real.sqrt_lt' (by linarith)]
          suffices a+b > 0 by linarith
          by_contra
          have : b = -a := by linarith
          contrapose h1
          unfold x2
          rw [this]
          simp
          ring_nf
          rw [show (9 + a * 6 + a ^ 2) = (a+3)^2 by linarith]
          rw [Real.sqrt_sq (by linarith)]
          ring_nf

  have hset3 : b ∈ Set.Icc (2*a) ((a^2+2*a+9)/4) → 
    ((a < 3 → S = {x0, -1/2 - a/2 - √(a^2+2*a+9-4*b)/2, -1/2 - a/2 + √(a^2+2*a+9-4*b)/2}) ∧ 
    (3 ≤ a → S = {x0})) := by
    intro ⟨h1, h2⟩
    let x1 := -1/2 - a/2 - √(a^2+2*a+9-4*b)/2
    let x2 := -1/2 - a/2 + √(a^2+2*a+9-4*b)/2
    suffices (a < 3 → S = {x0, x1, x2}) ∧ (3 ≤ a → S = {x0}) by
      unfold x1 x2 at this
      exact this

    constructor
    . intro ha_lt3
      ext x
      unfold S
      simp
      constructor
      . intro hx
        rw [hgx x] at hx
        split_ifs at hx with h1
        . right
          have : (x-x1) * (x-x2) = 0 := by
            ring_nf
            rw [show x^2 = 2-x-a*x-b by linarith]
            rw [Real.sq_sqrt (by linarith)]
            ring_nf

          simp at this
          rcases this with h | h
          . left; linarith
          . right; linarith

        . left
          unfold x0
          field_simp
          linarith
        
      . rintro (rfl | rfl | rfl)
        . rw [hgx x0]
          split_ifs with h3
          . simp at h3
            have := h3.1
            unfold x0 at this
            rw [lt_div_iff₀ ha] at this
            linarith
          . unfold x0
            field_simp
            ring
        . rw [hgx x1]
          split_ifs with h3
          . ring_nf
            rw [Real.sq_sqrt (by linarith)]
            ring_nf
          . contrapose h3
            simp
            unfold x1
            constructor
            . suffices √(a ^ 2 + 2 * a + 9 - 4 * b) < 3 - a by linarith
              rw [Real.sqrt_lt' (by linarith)]
              by_contra
              have : 2*a=b := by linarith
              contrapose h3
              unfold x1
              simp
              rw [← this]
              field_simp
              ring_nf
              rw [show (9 - a * 6 + a ^ 2) = (3-a)^2 by linarith]
              rw [Real.sqrt_sq (by linarith)]
              ring_nf
 
            . suffices -3 - a < √(a ^ 2 + 2 * a + 9 - 4 * b) by linarith
              have : √(a ^ 2 + 2 * a + 9 - 4 * b) ≥ 0 := by positivity
              linarith

        . rw [hgx x2]
          split_ifs with h3
          . ring_nf
            rw [Real.sq_sqrt (by linarith)]
            ring_nf
          . contrapose h3
            simp
            unfold x2
            constructor
            . suffices a - 3 < √(a ^ 2 + 2 * a + 9 - 4 * b) by linarith
              have : √(a ^ 2 + 2 * a + 9 - 4 * b) ≥ 0 := by positivity
              linarith
            . suffices √(a ^ 2 + 2 * a + 9 - 4 * b) < 3 + a by linarith
              rw [Real.sqrt_lt' (by linarith)]
              linarith
    . intro ha_ge3
      ext x
      unfold S
      simp
      constructor
      . intro hx
        rw [hgx x] at hx
        split_ifs at hx with h1
        . have : (x-x1) * (x-x2) = 0 := by
            ring_nf
            rw [show x^2 = 2-x-a*x-b by linarith]
            rw [Real.sq_sqrt (by linarith)]
            ring_nf

          simp at this
          rcases this with h | h
          . have : x = x1 := by linarith
            rw [this] at h1
            simp at h1
            have := h1.1
            unfold x1 at this
            have : √(a ^ 2 + 2 * a + 9 - 4 * b) < 3 - a := by linarith
            have : √(a ^ 2 + 2 * a + 9 - 4 * b) ≥ 0 := by positivity
            linarith
          . have : x = x2 := by linarith
            rw [this] at h1
            simp at h1
            have := h1.2
            unfold x2 at this
            have : √(a ^ 2 + 2 * a + 9 - 4 * b) < 3 + a := by linarith
            rw [Real.sqrt_lt' (by linarith)] at this
            nlinarith
        . unfold x0
          field_simp
          linarith
      . rintro rfl
        . rw [hgx x0]
          split_ifs with h1
          . simp at h1
            have := h1.1
            rw [lt_div_iff₀ ha] at this
            linarith
          . unfold x0
            field_simp
            linarith

  have hset4 : (a^2+2*a+9)/4 < b → S = {x0} := by
    intro h
    ext x
    unfold S
    simp
    constructor
    . intro hx
      rw [hgx x] at hx
      split_ifs at hx with h1
      . nlinarith [sq_nonneg (x+1/2+a/2)]
      . unfold x0
        field_simp
        linarith
    . intro hx
      rw [hgx x, hx]
      unfold x0
      split_ifs with h1
      . simp at h1
        have := h1.1
        rw [lt_div_iff₀ ha] at this
        linarith
      . field_simp
        linarith

  refine ⟨hgx, ⟨?_, ?_⟩⟩
  . intro h
    have h1 : b ≥ -a := by
      by_contra h1
      simp at h1
      have := hset1 h1
      unfold S at this
      rw [this] at h
      simp at h
    
    have h2 : 2*a ≤ b := by
      by_contra h2
      simp at h2
      have := hset2 ⟨h1, h2⟩
      unfold S at this
      rw [this] at h
      simp at h

    rcases lt_trichotomy b ((a^2+2*a+9)/4) with h3 | rfl | h4
    . have := hset3 (by constructor <;> linarith)
      by_cases ha_lt3 : a < 3
      . have := this.1 ha_lt3
        unfold S at this
        rw [this] at h

        refine ⟨ha_lt3, ⟨?_, h3⟩⟩
        by_contra
        have : 2*a = b := by linarith
        unfold x0 at h
        rw [← this] at h
        ring_nf at h
        rw [show (9 - a * 6 + a ^ 2) = (3-a)^2 by linarith] at h
        rw [Real.sqrt_sq (by linarith)] at h
        ring_nf at h
        field_simp at h
        rw [Set.encard_pair (by linarith)] at h
        norm_num at h

      . simp at ha_lt3
        have := this.2 ha_lt3
        unfold S at this
        rw [this] at h
        simp at h

    . have := hset3 (by simp; linarith)
      unfold S at this
      by_cases ha_lt3 : a < 3
      . rw [this.1 ha_lt3] at h
        ring_nf at h
        field_simp at h
        by_cases heq : ((-(a * 4) + -(a ^ 2 * 2)) * (a * 4) + -(9 * (2 * (a * 4)))) / (2 * (a * 4) * (a * 4)) = (-1 + -a) / 2
        . rw [heq] at h
          simp at h
        . rw [Set.encard_pair heq] at h
          norm_num at h
      . simp at ha_lt3
        rw [this.2 ha_lt3] at h
        simp at h

    . have := hset4 h4
      unfold S at this
      rw [this] at h
      simp at h

  . intro ⟨ha_lt3, ⟨h1, h2⟩⟩
    let x1 := -(1+a)/2 - √(a^2+2*a+9-4*b)/2
    let x2 := -(1+a)/2 + √(a^2+2*a+9-4*b)/2

    have hx0 : x0 < -2 := by
      rw [div_lt_iff₀ ha]
      linarith

    have hx1 : x1 ∈ Set.Ioo (-2) 1 := by
      simp
      unfold x1
      constructor
      . suffices √(a ^ 2 + 2 * a + 9 - 4 * b) < 3 - a by linarith
        rw [Real.sqrt_lt' (by linarith)]
        linarith
      . have : √(a ^ 2 + 2 * a + 9 - 4 * b) ≥ 0 := by positivity
        linarith

    have hx2 : x2 ∈ Set.Ioo (-2) 1 := by
      simp
      unfold x2
      constructor
      . have : √(a ^ 2 + 2 * a + 9 - 4 * b) ≥ 0 := by positivity
        linarith
      . suffices √(a ^ 2 + 2 * a + 9 - 4 * b) < 3 + a by linarith
        rw [Real.sqrt_lt' (by linarith)]
        linarith

    have hx12 : x1 ≠ x2 := by
      by_contra h
      unfold x1 x2 at h
      have : √(a ^ 2 + 2 * a + 9 - 4 * b) = 0 := by
        linarith

      rw [Real.sqrt_eq_zero'] at this
      linarith


    suffices {x | g x = a * x + b} = {x0, x1, x2} by
      rw [this, Set.encard_insert_of_not_mem (by
        rintro (h1 | h2)
        . simp at hx1; linarith
        . simp at hx2 h2; linarith
      ), Set.encard_pair hx12]
      norm_num

    ext x; simp
    constructor
    . intro hx
      rw [hgx x] at hx
      split_ifs at hx with h1
      . right
        have : (x-x1) * (x-x2) = 0 := by
          ring_nf
          rw [show x^2 = 2-x-a*x-b by linarith]
          rw [Real.sq_sqrt (by linarith)]
          ring_nf

        simp at this
        rcases this with h | h
        . left; linarith
        . right; linarith

      . left
        unfold x0
        field_simp
        linarith

    . rintro (rfl | rfl | rfl)
      . rw [hgx x0]
        split_ifs with h1
        . simp at h1
          linarith
        . unfold x0
          field_simp
          ring
      all_goals
      . try rw [hgx x1]
        try rw [hgx x2]
        split_ifs
        try unfold x1 x2
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        ring_nf
