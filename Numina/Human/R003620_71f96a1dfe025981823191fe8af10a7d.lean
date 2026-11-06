import Mathlib
open Real Set

set_option maxHeartbeats 1000000

theorem algebra_202265 :
  {a : ℝ | {x : ℝ | 1 < x ∧ x < 2 ∧ 0 < a * x + 1 ∧ logb 10 (a * x + 1) = logb 10 (x - 1) + logb 10 (2 - x)}.encard = 1} =
  {a : ℝ | a ∈ Ioc (-1) (-1/2) ∨ a = (3-2*√3)} := by

  have : √3 > 0 := by positivity
  have : √3 < 7 / 4 := by
    rw [sqrt_lt (by norm_num) (by norm_num)]
    norm_num

  have hs1 : √12 = 2*√3 := by
    rw [sqrt_eq_cases]
    left
    constructor
    . ring_nf
      rw [sq_sqrt (by linarith)]
      norm_num
    . linarith

  ext a; simp

  let S := {x | 1 < x ∧ x < 2 ∧ 0 < a * x + 1 ∧ logb 10 (a * x + 1) = logb 10 (x - 1) + logb 10 (2 - x)}
  let T := {x | 1 < x ∧ x < 2 ∧ 0 < a * x + 1 ∧ (a * x + 1) = (x - 1) * (2 - x)}

  have hT : S = T := by
    unfold S T
    ext x
    simp
    intro hx1 hx2 hx3
    rw [← logb_mul (by linarith) (by linarith)]
    constructor
    . have : (x - 1) * (2 - x) ∈ Ioi 0 := by
        simp
        nlinarith
      apply logb_injOn_pos (by linarith) hx3 this
    . intro h
      rw [h]

  have h_set1: a ∉ Ioc (-1) (3-2*√3) → S = ∅ := by
    intro ha
    simp at ha
    ext x
    rw [hT]; unfold T
    simp
    intro hx1 hx2 hx3 heq
    by_cases ha1 : (a-3)^2 < 12
    . have : (x+a/2-3/2)^2 ≥ 0 := by positivity
      have : (x+a/2-3/2)^2 = (a^2-6*a-3)/4:= by
        ring_nf
        have : x * a = -3 + (x * 3 - x ^ 2) := by linarith
        rw [this]
        ring_nf
      linarith

    . simp at ha1
      -- have ha2: -3 - a * 6 + a ^ 2 ≥ 0 := by linarith
      have : (x-(3/2-a/2-√(a^2-6*a-3)/2))*(x-(3/2-a/2+√(a^2-6*a-3)/2)) = 0 := by
        ring_nf
        rw [sq_sqrt (by linarith)]
        ring_nf at heq
        have : x * a = -3 + (x * 3 - x ^ 2) := by linarith
        rw [this]
        ring_nf

      simp at this
      rcases this with hx3 | hx4
      . have :  x = (3 / 2 - a / 2 - √(a ^ 2 - 6 * a - 3) / 2) := by linarith
        by_cases ha2 : -1 < a
        . have ha3 := ha ha2
          have : a ≥ 3+2*√3 := by
            have : (2*√3)^2 ≤ (a-3)^2 := by
              ring_nf
              rw [sq_sqrt (by linarith)]
              linarith
            rw [sq_le_sq] at this
            rw [abs_of_pos (by linarith)] at this
            by_cases ha4 : a ≥ 3
            . rw [abs_of_nonneg (by linarith)] at this
              linarith
            . simp at ha4
              rw [abs_of_neg (by linarith)] at this
              linarith

          have : x < 0 := by
            subst x
            suffices 3 - a < √(a ^ 2 - 6 * a - 3) by linarith
            have : √(a ^ 2 - 6 * a - 3) ≥ 0 := by positivity
            linarith
          linarith

        . simp at ha2
          have : x ≤ 1 := by
            subst x
            suffices 1 - a ≤ √(a ^ 2 - 6 * a - 3) by linarith
            rw [le_sqrt (by linarith) (by linarith)]
            linarith

          linarith

      . have : x = (3 / 2 - a / 2 + √(a ^ 2 - 6 * a - 3) / 2) := by linarith
        by_cases ha2 : -1 < a
        . have ha3 := ha ha2
          have : a ≥ 3+2*√3 := by
            have : (2*√3)^2 ≤ (a-3)^2 := by
              ring_nf
              rw [sq_sqrt (by linarith)]
              linarith
            rw [sq_le_sq] at this
            rw [abs_of_pos (by linarith)] at this
            by_cases ha4 : a ≥ 3
            . rw [abs_of_nonneg (by linarith)] at this
              linarith
            . simp at ha4
              rw [abs_of_neg (by linarith)] at this
              linarith
          have : x < 0 := by
            suffices √(a ^ 2 - 6 * a - 3) < a - 3 by linarith
            rw [sqrt_lt (by linarith) (by linarith)]
            linarith
          linarith

        . simp at ha2
          have : x ≥ 3 := by
            have : √(a ^ 2 - 6 * a - 3) ≥ 0 := by positivity
            linarith
          linarith

  have h_set2: a ∈ Ioc (-1) (-1/2) → S = {3/2-a/2-√(a^2-6*a-3)/2} := by
    intro ha
    have ha1 : 0 ≤ -3 - a * 6 + a ^ 2 := by
      have ⟨ ha1,ha2 ⟩ := ha
      suffices (2*√3)^2 ≤ (a-3)^2 by
        ring_nf at this
        rw [sq_sqrt (by linarith)] at this
        linarith

      rw [sq_le_sq]
      rw [abs_of_pos (by linarith)]
      rw [abs_of_neg (by nlinarith)]
      nlinarith
    have ⟨ ha2, ha3 ⟩ := ha
    have ha4: a < 0 := by nlinarith
    have ha5: a ≠ 0 := by linarith
    have ha6: √(a ^ 2 - 6 * a - 3) ≥ 0 := by positivity
    ext x
    rw [hT]; unfold T
    simp
    constructor
    . intro ⟨ hx1, hx2, hx3, heq ⟩
      have : (x-(3/2-a/2-√(a^2-6*a-3)/2))*(x-(3/2-a/2+√(a^2-6*a-3)/2)) = 0 := by
        ring_nf
        rw [sq_sqrt (by linarith)]
        ring_nf at heq
        have : x * a = -3 + (x * 3 - x ^ 2) := by linarith
        rw [this]
        ring_nf

      simp at this
      rcases this with hx4 | hx5
      . linarith
      .
        nlinarith

    . intro hx
      rw [hx]
      have : √(a ^ 2 - 6 * a - 3) ≥ 0 := by positivity
      refine ⟨?_, ?_, ?_, ?_ ⟩
      . suffices √(a ^ 2 - 6 * a - 3) < 1 - a by linarith
        rw [sqrt_lt (by linarith) (by linarith)]
        nlinarith
      . linarith
      . suffices a*√(a ^ 2 - 6 * a - 3) < (3*a - a^2) + 2 by linarith
        by_cases ha7 : 3*a - a^2 + 2 > 0
        . nlinarith
        . simp at ha7
          suffices |3*a - a^2 + 2| < |a*√(a ^ 2 - 6 * a - 3)| by
            rw [abs_of_nonpos (by linarith)] at this
            rw [abs_of_nonpos (by nlinarith)] at this
            linarith
          rw [← sq_lt_sq]
          ring_nf
          rw [sq_sqrt (by linarith)]
          nlinarith
      . ring_nf
        rw [sq_sqrt (by linarith)]
        ring_nf

  have h_set3: a ∈ Ioc (-1/2) (3-2*√3) → S = {3/2-a/2-√(a^2-6*a-3)/2, 3/2-a/2+√(a^2-6*a-3)/2} := by
    intro ha

    have ha1 : 0 ≤ -3 - a * 6 + a ^ 2 := by
      have ⟨ ha1,ha2 ⟩ := ha
      suffices (2*√3)^2 ≤ (a-3)^2 by
        ring_nf at this
        rw [sq_sqrt (by linarith)] at this
        linarith

      rw [sq_le_sq]
      rw [abs_of_pos (by linarith)]
      rw [abs_of_neg (by nlinarith)]
      nlinarith
    have ⟨ ha2, ha3 ⟩ := ha
    have ha4: a < 0 := by nlinarith
    have ha5: a ≠ 0 := by linarith
    have ha6: √(a ^ 2 - 6 * a - 3) ≥ 0 := by positivity

    ext x
    rw [hT]; unfold T
    simp
    constructor
    . intro ⟨ hx1, hx2, hx3, heq ⟩
      have : (x-(3/2-a/2-√(a^2-6*a-3)/2))*(x-(3/2-a/2+√(a^2-6*a-3)/2)) = 0 := by
        ring_nf
        rw [sq_sqrt ha1]
        ring_nf at heq
        have : x * a = -3 + (x * 3 - x ^ 2) := by linarith
        rw [this]
        ring_nf

      simp at this
      rcases this with hx1 | hx2
      . left; linarith
      . right; linarith

    . intro hx
      rcases hx with hx1 | hx2
      all_goals subst x; refine ⟨?_, ?_, ?_, ?_ ⟩
      . suffices  √(a ^ 2 - 6 * a - 3) < 1 - a by linarith
        rw [sqrt_lt (by linarith) (by nlinarith)]
        linarith
      . linarith
      . suffices a*√(a ^ 2 - 6 * a - 3) < 3*a - a^2 + 2 by
          linarith

        have : 3*a - a^2 + 2 > 0 := by
          suffices a^2 -3*a- 2 < 3 + a * 6 - a ^ 2 by linarith
          suffices (2*a+1)*(a-5)<0 by linarith
          nlinarith
        nlinarith

      . ring_nf; rw [sq_sqrt ha1]; ring_nf
      . nlinarith
      . suffices √(a ^ 2 - 6 * a - 3) < a + 1 by linarith
        rw [sqrt_lt (by linarith) (by nlinarith)]
        linarith
      . suffices a^2-3*a-2 < a*√(a ^ 2 - 6 * a - 3) by linarith
        have : 3*a - a^2 + 2 > 0 := by
          suffices a^2 -3*a- 2 < 3 + a * 6 - a ^ 2 by linarith
          suffices (2*a+1)*(a-5)<0 by linarith
          nlinarith

        suffices |a*√(a ^ 2 - 6 * a - 3)| < |3*a - a^2 + 2| by
          rw [abs_of_nonpos (by nlinarith)] at this
          rw [abs_of_pos (by linarith)] at this
          linarith

        rw [← sq_lt_sq]
        ring_nf
        rw [sq_sqrt ha1]
        suffices (a+1)*(2*a+1) > 0 by linarith
        nlinarith

      . ring_nf; rw [sq_sqrt ha1]; ring_nf

  suffices S.encard = 1 ↔ a ∈ Ioc (-1) (-1/2) ∨ a = (3-2*√3) by
    tauto

  constructor
  . intro h
    by_cases ha1: a ∈ Ioc (-1) (3-2*√3)
    . by_cases ha2: a ∈ Ioc (-1) (-1/2)
      . left; exact ha2
      . right
        have ha3 : a ∈ Ioc (-1/2) (3-2*√3) := by
          simp at ha1 ha2 ⊢
          constructor
          . exact ha2 ha1.1
          . exact ha1.2

        have := h_set3 ha3
        rw [this] at h
        by_contra ha4
        rw [Set.encard_pair] at h
        norm_num at h
        by_contra ha5
        have : √(a ^ 2 - 6 * a - 3) = 0 := by linarith
        rw [sqrt_eq_zero'] at this
        have : (a-3)^2 ≤ 12 := by linarith
        have : (a-3)^2 ≤ (2*√3)^2 := by
          ring_nf
          rw [sq_sqrt (by norm_num)]
          linarith

        rw [sq_le_sq] at this
        simp at ha3
        rw [abs_of_neg (by linarith)] at this
        rw [abs_of_pos (by linarith)] at this
        have : a = 3-2*√3 := by linarith
        contradiction

    . have := h_set1 ha1
      rw [this] at h
      simp at h

  . intro h
    rcases h with h1 | h2
    . have := h_set2 h1
      rw [this]
      simp
    . subst a
      have := h_set3 (by simp; linarith)
      rw [this]
      ring_nf
      rw [sq_sqrt (by norm_num)]
      ring_nf
      simp
