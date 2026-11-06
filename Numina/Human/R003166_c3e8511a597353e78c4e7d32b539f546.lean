import Mathlib

set_option maxHeartbeats 500000

theorem alegbra_158437
  (c : ℝ)
  (f : ℝ → ℝ)
  (hf : f = λ x => x^2 + 6 * x + c) :
  {x | f (f x) = 0}.encard = 3 ↔ c = 11/2 - √13/2 := by

  have h_calc_1: √(1 + √13) ^ 4 = 14 + 2*√13 := by
    rw [show 4 = 2*2 by norm_num]
    rw [pow_mul]
    rw [Real.sq_sqrt (by positivity)]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring_nf


  let m := 11/2 - √13/2
  let m' := 11/2 + √13/2

  have hm' : m' < 9 := by
    suffices √13 < 7 by unfold m'; linarith
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num

  let x1 := -3 - √(6-c-√(9-c))
  let x2 := -3 + √(6-c-√(9-c))
  let x3 := -3 - √(6-c+√(9-c))
  let x4 := -3 + √(6-c+√(9-c))

  let S := {x | f (f x) = 0}
  have hset1 : c > m' → S = ∅ := by
    intro hc
    unfold m' at hc
    unfold S
    ext x
    simp
    let y := f x
    rw [← (show y = f x by rfl), hf]
    simp
    by_cases hc1 : c > 9
    . nlinarith [sq_nonneg (y+3)]
    . simp at hc1
      by_contra h
      have : (y-(-3-√(9-c))) * (y-(-3+√(9-c))) = 0 := by
        rw [← h]
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        ring
      simp at this
      rcases this with h | h
      . unfold y at h
        rw [hf] at h
        simp at h
        have : √(9 - c) ≤ 6 - c := by
          nlinarith [sq_nonneg (x+3)]
        
        rw [Real.sqrt_le_iff] at this
        have : c ≤ 6 := by linarith
        have : m' < c := hc
        have : m' < 6 := by linarith
        unfold m' at this
        have : 1 < √13 := by
          rw [Real.lt_sqrt (by norm_num)]
          norm_num
        linarith
      . unfold y at h
        rw [hf] at h
        simp at h
        have : c - 6 ≤ √(9 - c) := by
          nlinarith [sq_nonneg (x+3)]

        have hc2 : 0 ≤ c - 6 := by
          have : 1 < √13 := by
            rw [Real.lt_sqrt (by norm_num)]
            norm_num
          linarith

        rw [Real.le_sqrt hc2 (by linarith)] at this
        have : (c-m)*(c-m') ≤ 0 := by
          ring_nf
          rw [Real.sq_sqrt (by linarith)]
          nlinarith

        rw [mul_nonpos_iff] at this
        rcases this with h | ⟨h1, h2⟩
        . have : m' < c := hc
          linarith
        . have : c ≤ m := by linarith
          have : m' < c := hc
          have : m' < m := by linarith
          unfold m m' at this
          have : 0 < √13 := by positivity
          linarith

  have hset2 : c ∈ Set.Ioc m m' → S = {x3, x4} := by
    intro ⟨hc1, hc2⟩
    unfold S
    ext x
    let y := f x
    simp
    rw [← (show y = f x by rfl), hf]
    simp

    have hc0 : 0 ≤ 6 - c + √(9 - c) := by
      suffices c - 6 ≤ √(9 - c) by linarith
      apply Real.le_sqrt_of_sq_le
      suffices (c-m)*(c-m') ≤ 0 by
        ring_nf at this
        rw [Real.sq_sqrt (by linarith)] at this
        nlinarith
      rw [mul_nonpos_iff]
      left
      constructor <;> linarith

    constructor
    . intro h
      have : (y-(-3-√(9-c))) * (y-(-3+√(9-c))) = 0 := by
        rw [← h]
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        ring
      simp at this
      rcases this with h | h
      . exfalso
        unfold y at h
        rw [hf] at h
        simp at h
        have : √(9 - c) ≤ 6 - c := by
          nlinarith [sq_nonneg (x+3)]
        
        rw [Real.sqrt_le_iff] at this
        have : (m-c)*(c-m') ≤ 0 := by
          ring_nf
          rw [Real.sq_sqrt (by linarith)]
          nlinarith

        rw [mul_nonpos_iff] at this
        rcases this with h | ⟨h1, h2⟩
        . linarith
        . have : m' ≤ c := by linarith
          have : c ≤ 6 := by linarith
          have : m' ≤ 6 := by linarith
          unfold m' at this
          have : 1 < √13 := by
            rw [Real.lt_sqrt (by norm_num)]
            norm_num
          linarith


      . unfold y at h
        rw [hf] at h
        simp at h
        have : (x-x3)*(x-x4) = 0 := by
          rw [← h]
          ring_nf
          rw [Real.sq_sqrt hc0]
          ring
        simp at this
        rcases this with h | h
        . left; linarith
        . right; linarith
    . intro h
      suffices y = -3 + √(9-c) by
        rw [this]
        ring_nf
        rw [Real.sq_sqrt (by linarith)]
        norm_num

      unfold y
      rw [hf]
      simp
      rcases h with rfl | rfl
      all_goals
      . ring_nf
        rw [Real.sq_sqrt hc0]
        ring

  have hset3 : c ≤ m → S = {x1, x2, x3, x4} := by
    intro hc
    unfold S
    ext x
    let y := f x
    simp
    rw [← (show y = f x by rfl), hf]
    simp

    have hc1 : 0 ≤ 9 - c := by
      suffices m < 9 by linarith
      unfold m
      have : √13 > 0 := by positivity
      linarith

    have hc2 : 0 ≤ 6 + (-c - √(9 - c)) := by
      suffices √(9 - c) ≤ 6 - c by linarith
      rw [Real.sqrt_le_iff]
      constructor
      . suffices m < 6 by linarith
        unfold m
        have : √13 > 0 := by positivity
        linarith
      . suffices (m-c)*(c-m') ≤ 0 by
          ring_nf at this
          rw [Real.sq_sqrt (by linarith)] at this
          nlinarith
        rw [mul_nonpos_iff]
        left
        constructor
        . linarith
        . suffices m ≤ m' by linarith
          unfold m m'
          have : √13 > 0 := by positivity
          linarith

    have hc3 : 0 ≤ 6 - c + √(9 - c) := by
      suffices c - 6 ≤ √(9 - c) by linarith
      have : c < 6 := by
        suffices m < 6 by linarith
        unfold m
        have : √13 > 0 := by positivity
        linarith
      have : √(9 - c) ≥ 0 := by positivity
      linarith

    constructor
    . intro h
      have : (y-(-3-√(9-c))) * (y-(-3+√(9-c))) = 0 := by
        rw [← h]
        ring_nf
        rw [Real.sq_sqrt hc1]
        ring
      simp at this
      rcases this with h | h
      . unfold y at h
        rw [hf] at h
        simp at h
        have : (x-x1)*(x-x2) = 0 := by
          rw [← h]
          ring_nf
          rw [Real.sq_sqrt hc2]
          ring
        simp at this
        rcases this with h | h
        . left; linarith
        . right; left; linarith
      . right; right
        unfold y at h
        rw [hf] at h
        simp at h
        have : (x-x3)*(x-x4) = 0 := by
          rw [← h]
          ring_nf
          rw [Real.sq_sqrt hc3]
          ring
        simp at this
        rcases this with h | h
        . left; linarith
        . right; linarith

    . rintro (rfl | rfl | rfl | rfl)
      all_goals 
      . unfold y
        rw [hf]
        simp
        ring_nf
        simp only [show 4 = 2*2 by norm_num]
        rw [pow_mul, Real.sq_sqrt (by linarith)]
        ring_nf
        rw [Real.sq_sqrt hc1]
        ring

  constructor
  . intro h
    by_cases hc1 : c > m'
    . have := hset1 hc1
      unfold S at this
      rw [this] at h
      simp at h
    . by_cases hc2 : c ∈ Set.Ioc m m'
      . have := hset2 hc2
        unfold S at this
        rw [this] at h
        by_cases hx : x3 = x4
        . rw [hx] at h
          simp at h
        . rw [Set.encard_pair hx] at h
          norm_num at h
      . have hc3 : c ≤ m := by
          by_contra h
          simp at hc1 hc2 h
          have := hc2 h
          linarith
        have := hset3 hc3
        unfold S at this
        rw [this] at h
        by_cases hx : x1 = x2
        . unfold x1 x2 at hx
          have hc1 : 0 ≤ 6 - c := by
            suffices c ≤ 6 by linarith
            suffices m ≤ 6 from le_trans hc3 this
            unfold m
            have : √13 > 0 := by positivity
            linarith

          have : √(6 - c - √(9 - c)) = 0 := by linarith
          rw [Real.sqrt_eq_zero'] at this
          have : 6 - c ≤ √(9 - c) := by linarith
          rw [Real.le_sqrt hc1 (by linarith)] at this


          have : (c-m)*(c-m') ≤ 0 := by
            ring_nf
            rw [Real.sq_sqrt (by norm_num)]
            linarith

          rw [mul_nonpos_iff] at this
          rcases this with h | ⟨h1, h2⟩
          . by_contra hc
            have := lt_of_le_of_ne hc3 hc
            linarith
          . have : √13 > 0 := by positivity
            have : m' ≤ c := by linarith
            have : m' ≤ m := by apply le_trans this hc3
            unfold m m' at this
            linarith

        . have hc4 : c < 6 := by
            suffices m < 6 by linarith
            unfold m
            have : √13 > 0 := by positivity
            linarith

          have hc5 : 0 ≤ 6 - c - √(9 - c) := by
            suffices √(9 - c) ≤ 6 - c by linarith
            rw [Real.sqrt_le_iff]
            constructor
            . linarith
            . suffices (m-c)*(c-m') ≤ 0 by
                ring_nf at this
                rw [Real.sq_sqrt (by linarith)] at this
                nlinarith
              rw [mul_nonpos_iff]
              left
              constructor <;> linarith

          have hc6 : 0 ≤ 6 - c + √(9 - c) := by
            have : √(9 - c) ≥ 0 := by positivity
            linarith

          have hc7 : 0 ≤ √(6 - c + √(9 - c)) := by
            rw [Real.le_sqrt (by linarith) (by linarith)]
            linarith

          have : x1 ∉ ({x2, x3, x4}: Set ℝ) := by
            simp
            refine ⟨hx, ?_, ?_⟩
            . by_contra h
              unfold x1 x3 at h
              have : √(6 - c - √(9 - c)) = √(6 - c + √(9 - c)) := by linarith
              rw [Real.sqrt_eq_iff_mul_self_eq hc5 hc7] at this
              ring_nf at this
              rw [Real.sq_sqrt hc6] at this
              have : √(9 - c) = 0 := by linarith
              rw [Real.sqrt_eq_zero'] at this
              linarith

            . by_contra h
              unfold x1 x4 at h
              have : √(6 - c - √(9 - c)) = - √(6 - c + √(9 - c)) := by linarith
              have : √(6 - c - √(9 - c)) ≥ 0 := by positivity
              have : √(6 - c + √(9 - c)) ≥ 0 := by positivity
              have : √(6 - c - √(9 - c)) = 0 := by linarith
              rw [Real.sqrt_eq_zero'] at this
              have : √(6 - c + √(9 - c)) = 0 := by linarith
              rw [Real.sqrt_eq_zero'] at this
              linarith
          rw [Set.encard_insert_of_not_mem this] at h
          have : x2 ∉ ({x3, x4}: Set ℝ) := by
            simp; constructor
            . by_contra h
              unfold x2 x3 at h
              have : √(6 - c - √(9 - c)) = - √(6 - c + √(9 - c)) := by linarith
              have : √(6 - c - √(9 - c)) ≥ 0 := by positivity
              have : √(6 - c + √(9 - c)) ≥ 0 := by positivity
              have : √(6 - c - √(9 - c)) = 0 := by linarith
              rw [Real.sqrt_eq_zero'] at this
              have : √(6 - c + √(9 - c)) = 0 := by linarith
              rw [Real.sqrt_eq_zero'] at this
              linarith
            . by_contra h
              unfold x2 x4 at h
              have : √(6 - c - √(9 - c)) = √(6 - c + √(9 - c)) := by linarith
              rw [Real.sqrt_eq_iff_mul_self_eq hc5 hc7] at this
              ring_nf at this
              rw [Real.sq_sqrt hc6] at this
              have : √(9 - c) = 0 := by linarith
              rw [Real.sqrt_eq_zero'] at this
              linarith


          rw [Set.encard_insert_of_not_mem this] at h
          have : x3 ≠ x4 := by
            by_contra h
            unfold x3 x4 at h
            have : √(6 - c + √(9 - c)) = 0 := by linarith
            rw [Real.sqrt_eq_zero'] at this
            have : √(9 - c) ≥ 0 := by positivity
            linarith

          rw [Set.encard_pair this] at h
          norm_num at h

  . intro h
    suffices {x | f (f x) = 0} = {-3, -3 - √(1+√13), -3 + √(1+√13)} by
      rw [this]
      have : -3 ∉ ({-3 - √(1 + √13), -3 + √(1 + √13)}: Set ℝ) := by
        simp
        constructor
        all_goals
        . by_contra h
          have : √(1 + √13) = 0 := by linarith
          rw [Real.sqrt_eq_zero'] at this
          have : 1 + √13 > 0 := by positivity
          linarith
      rw [Set.encard_insert_of_not_mem this]
      have : -3 - √(1 + √13) ≠ -3 + √(1 + √13) := by
        by_contra h
        have : √(1 + √13) = 0 := by linarith
        rw [Real.sqrt_eq_zero'] at this
        have : 1 + √13 > 0 := by positivity
        linarith

      rw [Set.encard_pair this]
      norm_num

    rw [hf, h]
    simp
    ext x
    simp
    constructor
    . intro h

      have : (x+3)^2 * (x^2 + 6*x + 8-√13) = 0 := by
        rw [← h]
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        ring

      simp at this
      rcases this with h | h
      . left; linarith
      . right
        have : (x-(-3-√(1+√13))) * (x-(-3+√(1+√13))) = 0 := by
          rw [← h]
          ring_nf
          rw [Real.sq_sqrt (by positivity)]
          ring
        simp at this
        rcases this with h | h
        . left; linarith
        . right; linarith
    . intro h
      rcases h with rfl | rfl | rfl
      . ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
      all_goals
      . ring_nf
        rw [h_calc_1, Real.sq_sqrt (by positivity)]
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
