import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_262557 (x : ℝ) :
  x + 6 - sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≥ 0 ↔ x ≥ -5 := by
  constructor
  · -- Assume $x + 6 - \sqrt{(x + 6) * |x + 5| + |x + 4|} \geq 0$
    intro h
    by_cases h1 : x ≥ -5
    · -- This case is trivial: x ≥ -5 is already our goal
      linarith
    · -- Case x < -5
      push_neg at h1
      by_cases h2 : x ≥ -6
      · -- Case -6 ≤ x < -5
        have h2' : x ≥ -6 := h2
        have h3 : x < -5 := h1
        have h4 : x + 6 ≥ 0 := by linarith
        have h5 : (x + 6) * abs (x + 5) + abs (x + 4) ≥ 0 := by
          apply add_nonneg
          · apply mul_nonneg
            linarith
            apply abs_nonneg
          · apply abs_nonneg
        have h6 : sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≥ 0 := Real.sqrt_nonneg _
        have h7 : x + 6 ≥ sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) := by linarith
        have h8 : (x + 6) ^ 2 ≥ ((x + 6) * abs (x + 5) + abs (x + 4)) := by
          have h9 : sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ^ 2 = ((x + 6) * abs (x + 5) + abs (x + 4)) := by
            rw [Real.sq_sqrt]
            linarith [h5]
          nlinarith [h7, h9, Real.sqrt_nonneg ((x + 6) * abs (x + 5) + abs (x + 4)), sq_nonneg (x + 6)]
        have h9 : (x + 5) ≤ 0 := by linarith
        have h10 : abs (x + 5) = -(x + 5) := abs_of_nonpos h9
        have h11 : (x + 4) ≤ 0 := by linarith
        have h12 : abs (x + 4) = -(x + 4) := abs_of_nonpos h11
        have h13 : (x + 6) * abs (x + 5) + abs (x + 4) = (x + 6) * (-(x + 5)) + (-(x + 4)) := by
          rw [h10, h12]
        rw [h13] at h8
        nlinarith [sq_nonneg (x + 6), sq_nonneg (x + 5), sq_nonneg (x + 4)]
      · -- Case x < -6
        push_neg at h2
        have h10 : x < -6 := by linarith
        have h11 : x + 6 < 0 := by linarith
        have h12 : sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) ≥ 0 := Real.sqrt_nonneg _
        have h13 : x + 6 < Real.sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) := by
          linarith
        linarith [Real.sqrt_nonneg ((x + 6) * abs (x + 5) + abs (x + 4)), h13]
  · -- Now prove the reverse direction: x ≥ -5 → x + 6 - √((x + 6)|x + 5| + |x + 4|) ≥ 0
    intro h
    by_cases h1 : x ≥ -4
    · -- Case x ≥ -4 (so |x + 5| = x + 5 and |x + 4| = x + 4)
      have h2 : abs (x + 5) = x + 5 := abs_of_nonneg (by linarith)
      have h3 : abs (x + 4) = x + 4 := abs_of_nonneg (by linarith)
      have h4 : sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) = Real.sqrt ((x + 6) * (x + 5) + (x + 4)) := by
        rw [h2, h3]
      rw [h4]
      have h5 : (x + 6) * (x + 5) + (x + 4) ≥ 0 := by
        nlinarith [sq_nonneg (x + 5), sq_nonneg (x + 4)]
      have h6 : x + 6 ≥ Real.sqrt ((x + 6) * (x + 5) + (x + 4)) := by
        have h7 : (Real.sqrt ((x + 6) * (x + 5) + (x + 4))) ^ 2 = ((x + 6) * (x + 5) + (x + 4)) := by
          rw [Real.sq_sqrt]
          linarith [h5]
        have h8 : (x + 6) ^ 2 ≥ (Real.sqrt ((x + 6) * (x + 5) + (x + 4))) ^ 2 := by
          nlinarith [sq_nonneg (x + 6), Real.sqrt_nonneg ((x + 6) * (x + 5) + (x + 4)), h7]
        nlinarith [Real.sqrt_nonneg ((x + 6) * (x + 5) + (x + 4)), h8]
      linarith
    · -- Case -5 ≤ x < -4 (so |x + 5| = x + 5 and |x + 4| = -(x + 4))
      push_neg at h1
      have h2 : abs (x + 5) = x + 5 := abs_of_nonneg (by linarith)
      have h3 : abs (x + 4) = -(x + 4) := abs_of_nonpos (by linarith)
      have h4 : sqrt ((x + 6) * abs (x + 5) + abs (x + 4)) = Real.sqrt ((x + 6) * (x + 5) + (-(x + 4))) := by
        rw [h2, h3]
      rw [h4]
      have h5 : (x + 6) * (x + 5) + (-(x + 4)) ≥ 0 := by
        nlinarith [sq_nonneg (x + 5), sq_nonneg (x + 4)]
      have h6 : x + 6 ≥ Real.sqrt ((x + 6) * (x + 5) + (-(x + 4))) := by
        have h7 : (Real.sqrt ((x + 6) * (x + 5) + (-(x + 4)))) ^ 2 = ((x + 6) * (x + 5) + (-(x + 4))) := by
          rw [Real.sq_sqrt]
          linarith [h5]
        have h8 : (x + 6) ^ 2 ≥ (Real.sqrt ((x + 6) * (x + 5) + (-(x + 4)))) ^ 2 := by
          nlinarith [sq_nonneg (x + 6), Real.sqrt_nonneg ((x + 6) * (x + 5) + (-(x + 4))), h7]
        nlinarith [Real.sqrt_nonneg ((x + 6) * (x + 5) + (-(x + 4))), h8]
      linarith