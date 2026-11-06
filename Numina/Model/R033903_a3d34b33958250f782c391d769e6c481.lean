import Mathlib

open BigOperators Real Set

theorem inequalities_262557 (x : ℝ) :
  x + 6 - sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≥ 0 ↔ x ≥ -5 := by
  constructor
  · -- Forward direction: x + 6 - sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≥ 0 implies x ≥ -5
    intro h
    have h1 : x + 6 ≥ sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) := by
      linarith
    have h2 : x + 6 ≥ 0 := by
      by_contra h3
      push_neg at h3
      have h4 : sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≥ 0 := by positivity
      have h5 : x + 6 < 0 := h3
      have h6 : sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≥ x + 6 := by linarith
      nlinarith [Real.sqrt_nonneg ((x + 6) * abs (x + 5) + abs (x + 4)), Real.sq_sqrt (show (0 : ℝ) ≤ (x + 6) * abs (x + 5) + abs (x + 4) by
        cases' abs_cases (x + 5) with h1 h1
        · cases' abs_cases (x + 4) with h2 h2
          · -- Case x + 5 >= 0 and x + 4 >= 0
            nlinarith
          · -- Case x + 5 >= 0 and x + 4 < 0
            cases' abs_cases (x + 6) with h3 h3
            · nlinarith
            · nlinarith
        · cases' abs_cases (x + 4) with h2 h2
          · -- Case x + 5 < 0 and x + 4 >= 0
            cases' abs_cases (x + 6) with h3 h3
            · nlinarith
            · nlinarith
          · -- Case x + 5 < 0 and x + 4 < 0
            cases' abs_cases (x + 6) with h3 h3
            · nlinarith
            · nlinarith
      )
      ]
    have h3 : (sqrt ((x + 6) * abs (x + 5) + abs (x + 4))) ^ 2 = (x + 6) * abs (x + 5) + abs (x + 4) := by
      rw [Real.sq_sqrt]
      have h7 : (x + 6) * abs (x + 5) + abs (x + 4) ≥ 0 := by
        cases' abs_cases (x + 5) with h1 h1
        · cases' abs_cases (x + 4) with h2 h2
          · -- Case x + 5 >= 0 and x + 4 >= 0
            nlinarith
          · -- Case x + 5 >= 0 and x + 4 < 0
            cases' abs_cases (x + 6) with h3 h3
            · nlinarith
            · nlinarith
        · cases' abs_cases (x + 4) with h2 h2
          · -- Case x + 5 < 0 and x + 4 >= 0
            cases' abs_cases (x + 6) with h3 h3
            · nlinarith
            · nlinarith
          · -- Case x + 5 < 0 and x + 4 < 0
            cases' abs_cases (x + 6) with h3 h3
            · nlinarith
            · nlinarith
      linarith
    have h4 : (x + 6) ^ 2 ≥ (sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ) ^ 2 := by
      nlinarith [h2, Real.sqrt_nonneg ((x + 6) * abs (x + 5) + abs (x + 4))]
    have h5 : (x + 6) ^ 2 ≥ (x + 6) * abs (x + 5) + abs (x + 4) := by
      nlinarith [h3, h4, Real.sqrt_nonneg ((x + 6) * abs (x + 5) + abs (x + 4))]
    by_cases h10 : x ≥ -4
    · -- Case x ≥ -4
      rw [abs_of_nonneg (show x + 5 ≥ 0 by linarith), abs_of_nonneg (show x + 4 ≥ 0 by linarith)] at h5
      nlinarith
    · -- Case -5 ≤ x < -4
      by_cases h11 : x ≥ -5
      · -- Case -5 ≤ x < -4
        rw [abs_of_nonneg (show x + 5 ≥ 0 by linarith), abs_of_nonpos (show x + 4 ≤ 0 by linarith)] at h5
        nlinarith
      · -- Case x < -5
        rw [abs_of_nonpos (show x + 5 ≤ 0 by linarith), abs_of_nonpos (show x + 4 ≤ 0 by linarith)] at h5
        nlinarith [sq_nonneg (x + 5), sq_nonneg (x + 7)]
  · -- Backward direction: x ≥ -5 implies x + 6 - sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≥ 0
    intro h
    have h1 : x ≥ -5 := h
    have h2 : x + 6 ≥ 0 := by linarith
    have h3 : (x + 6) ^ 2 ≥ (x + 6) * abs (x + 5) + abs (x + 4) := by
      by_cases h10 : x ≥ -4
      · -- Case x ≥ -4
        rw [abs_of_nonneg (show x + 5 ≥ 0 by linarith), abs_of_nonneg (show x + 4 ≥ 0 by linarith)]
        nlinarith
      · -- Case -5 ≤ x < -4
        rw [abs_of_nonneg (show x + 5 ≥ 0 by linarith), abs_of_nonpos (show x + 4 ≤ 0 by linarith)]
        nlinarith
    have h6 : sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≤ x + 6 := by
      have h14 : sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≤ x + 6 := by
        have h20 : (sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ) ^ 2 ≤ (x + 6) ^ 2 := by
          have h22 : (sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ) ^ 2 = (x + 6) * abs (x + 5) + abs (x + 4) := by
            rw [Real.sq_sqrt]
            have h7 : (x + 6) * abs (x + 5) + abs (x + 4) ≥ 0 := by
              cases' abs_cases (x + 5) with h1 h1
              · cases' abs_cases (x + 4) with h2 h2
                · -- Case x + 5 >= 0 and x + 4 >= 0
                  nlinarith
                · -- Case x + 5 >= 0 and x + 4 < 0
                  nlinarith
              · cases' abs_cases (x + 4) with h2 h2
                · -- Case x + 5 < 0 and x + 4 >= 0
                  nlinarith
                · -- Case x + 5 < 0 and x + 4 < 0
                  nlinarith
            linarith
          nlinarith
        have h14' : sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≥ 0 := by positivity
        have h14'' : (x + 6) ≥ 0 := h2
        nlinarith [Real.sqrt_nonneg ((x + 6) * abs (x + 5) + abs (x + 4)), h20]
      linarith
    linarith