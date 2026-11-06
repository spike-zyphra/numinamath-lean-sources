import Mathlib

open Real

theorem algebra_230433 (a : ℝ) :
  (∃! (s: ℝ × ℝ), s.1 > 0 ∧ s.2 > 0 ∧ s.1 * 2 > s.2
    ∧ (∀ x, x^2 - 6 * x + a = (x - s.1) * (x - s.2))) ↔
  (0 < a ∧ a ≤ 8) ∨ a = 9 := by

  constructor
  . intro hs
    rcases hs with ⟨s, ⟨⟨hx, ⟨hy, ⟨hxy, heq⟩⟩⟩, hs⟩⟩
    by_cases ha1 : a > 9
    . have := heq s.1
      simp at this
      have : (s.1 - 3) ^ 2 ≥ 0 := by positivity
      linarith
    . simp at ha1
      by_cases ha2 : a = 9
      . right; assumption
      . have : a < 9 := lt_of_le_of_ne ha1 ha2
        by_cases ha3 : a > 8
        . have hs1 := hs (3 + √(9 - a), 3 - √(9 - a))
          simp at hs1
          have hs2 := hs (3 - √(9 - a), 3 + √(9 - a))
          simp at hs2

          have h1 : 0 < 3 + √(9 - a) := by
            have : √(9 - a) ≥ 0 := by positivity
            linarith
          have h2 : √(9 - a) < 3 := by
            rw [sqrt_lt' (by norm_num)]
            linarith
          have h3 : 3 - √(9 - a) < (3 + √(9 - a)) * 2 := by
            have : √(9 - a) ≥ 0 := by positivity
            linarith
          have h4 : (∀ (x : ℝ), x ^ 2 - 6 * x + a = (x - (3 + √(9 - a))) * (x - (3 - √(9 - a)))) := by
            intro x
            ring_nf
            rw [sq_sqrt (by nlinarith)]
            linarith

          have h5 : 3 + √(9 - a) < (3 - √(9 - a)) * 2 := by
            have : √(9 - a) < 1 := by
              rw [sqrt_lt' (by norm_num)]
              linarith
            linarith
          have h6 : (∀ (x : ℝ), x ^ 2 - 6 * x + a = (x - (3 - √(9 - a))) * (x - (3 + √(9 - a)))) := by
            intro x
            ring_nf
            rw [sq_sqrt (by nlinarith)]
            linarith


          have hs1 := hs1 h1 h2 h3 h4
          have hs2 := hs2 h2 h1 h5 h6
          rw [← hs2] at hs1
          simp at hs1
          have : √(9 - a) = 0 := by linarith
          rw [sqrt_eq_zero'] at this
          linarith

        . by_contra h_contra
          have ha4 : a ≤ 0 := by
            simp at h_contra
            by_contra h
            simp at h
            have := h_contra.1 h
            contradiction

          have := heq 0
          simp at this
          nlinarith

  . intro ha
    rcases ha with ⟨ha1, ha2⟩ | rfl
    . use (3 + √(9 - a), 3 - √(9 - a))
      simp
      constructor
      . constructor
        . have : √(9 - a) ≥ 0 := by positivity
          linarith
        . constructor
          . rw [sqrt_lt]
            all_goals linarith
          . constructor
            . have : √(9 - a) ≥ 0 := by positivity
              linarith
            . intro x
              ring_nf
              rw [sq_sqrt (by nlinarith)]
              ring_nf

      . intro x y hx hy hxy heq
        have := heq 0
        have : x * y = a := by linarith
        have := heq 1
        have : x + y = 6 := by linarith

        constructor
        . have := heq x
          simp at this
          have : (x - 3 - √(9 - a)) * (x - 3 + √(9 - a)) = 0 := by
            ring_nf
            rw [sq_sqrt (by nlinarith)]
            linarith
          simp at this
          rcases this with h1 | h2
          . linarith
          . have : x = 3 - √(9 - a) := by linarith
            rw [this] at hxy
            have : y = 3 + √(9 - a) := by linarith
            rw [this] at hxy
            have : √(9 - a) ≥ 0 := by positivity
            nlinarith

        . have := heq y
          simp at this
          have : (y - 3 - √(9 - a)) * (y - 3 + √(9 - a)) = 0 := by
            ring_nf
            rw [sq_sqrt (by nlinarith)]
            linarith
          simp at this
          rcases this with h1 | h2
          . have : y = 3 + √(9 - a) := by linarith
            rw [this] at hxy
            have : x = 3 - √(9 - a) := by linarith
            rw [this] at hxy
            have : √(9 - a) ≥ 0 := by positivity
            nlinarith
          . linarith

    . use (3, 3)
      simp
      constructor
      . intro x
        ring_nf
      . intro x y hx hy hxy heq
        have := heq x
        have := heq y
        have : (x - 3)^2= 0 := by linarith
        simp at this
        have : (y - 3)^2= 0 := by linarith
        simp at this
        constructor; all_goals linarith
