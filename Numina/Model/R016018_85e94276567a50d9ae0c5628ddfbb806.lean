import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_23091 (f : ℝ → ℝ) (hf : f = λ x => logb 2 (sqrt (sin x))) :
    {y | ∃ x, y = f x ∧ 0 < x ∧ x < π} = {y | y ≤ 0} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First, show that if y is in the range, then y ≤ 0
    rintro ⟨x, hy, hx1, hx2⟩
    have h1 : y = logb 2 (sqrt (sin x)) := by
      rw [hy]
      rw [hf]
    have h2 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith
    have h3 : sqrt (sin x) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h4 : sqrt (sin x) ≤ (1 : ℝ) := by
      have h5 : sin x ≤ 1 := by
        apply sin_le_one
      have h6 : sqrt (sin x) ≤ sqrt (1 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      have h7 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
    have h8 : logb 2 (sqrt (sin x)) ≤ (0 : ℝ) := by
      have h9 : sqrt (sin x) ≤ (1 : ℝ) := h4
      have h10 : sqrt (sin x) > 0 := by
        have h11 : sin x > 0 := h2
        have h12 : sqrt (sin x) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith
        linarith
      have h13 : logb 2 (sqrt (sin x)) ≤ logb 2 (1 : ℝ) := by
        apply Real.logb_le_logb_of_le
        all_goals
          try linarith
      have h14 : logb 2 (1 : ℝ) = 0 := Real.logb_one
      linarith
    linarith [h1, h8]
  · -- Now prove the reverse: if y ≤ 0, then there exists an x such that y = f(x)
    intro hy
    use Real.arcsin ((2 : ℝ) ^ (2 * y))
    constructor
    · -- Show that y = f (arcsin ((2 : ℝ) ^ (2 * y)))
      rw [hf]
      have h7 : Real.sin (Real.arcsin ((2 : ℝ) ^ (2 * y))) = (2 : ℝ) ^ (2 * y) := by
        apply Real.sin_arcsin
        · -- Show that -1 ≤ (2 : ℝ) ^ (2 * y)
          have h10 : (2 : ℝ) ^ (2 * y) ≥ 0 := by
            positivity
          linarith
        · -- Show that (2 : ℝ) ^ (2 * y) ≤ 1
          have h10 : (2 : ℝ) ^ (2 * y) ≤ (1 : ℝ) := by
            have h11 : (2 : ℝ) ^ (2 * y) ≤ (2 : ℝ) ^ (0 : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_le
              all_goals
                try linarith
            have h12 : (2 : ℝ) ^ (0 : ℝ) = 1 := by
              norm_num
            linarith
          linarith
      have h9 : Real.sqrt (Real.sin (Real.arcsin ((2 : ℝ) ^ (2 * y)))) = (2 : ℝ) ^ y := by
        rw [h7]
        have h10 : Real.sqrt ((2 : ℝ) ^ (2 * y : ℝ)) = (2 : ℝ) ^ y := by
          have h11 : ((2 : ℝ) ^ y) ^ 2 = (2 : ℝ) ^ (2 * y : ℝ) := by
            calc
              ((2 : ℝ) ^ y) ^ 2 = (2 : ℝ) ^ (y * 2 : ℝ) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul]
                ring
                all_goals
                  norm_num
              _ = (2 : ℝ) ^ (2 * y : ℝ) := by
                ring_nf
          have h12 : Real.sqrt ((2 : ℝ) ^ (2 * y : ℝ)) = (2 : ℝ) ^ y := by
            rw [← h11]
            have h13 : Real.sqrt (((2 : ℝ) ^ y) ^ 2) = (2 : ℝ) ^ y := by
              rw [Real.sqrt_sq (show (0 : ℝ) ≤ (2 : ℝ) ^ y by positivity)]
            linarith
          linarith
        linarith
      have h10 : Real.logb (2 : ℝ) (Real.sqrt (Real.sin (Real.arcsin ((2 : ℝ) ^ (2 * y))))) = y := by
        rw [h9]
        have h11 : Real.logb (2 : ℝ) ((2 : ℝ) ^ y) = y := by
          rw [Real.logb_rpow]
          all_goals
            norm_num
        linarith
      simp [h10]
    constructor
    · -- Show that 0 < arcsin ((2 : ℝ) ^ (2 * y))
      have h13 : Real.arcsin ((2 : ℝ) ^ (2 * y)) > 0 := by
        have h14 : (2 : ℝ) ^ (2 * y) > 0 := by positivity
        have h15 : Real.arcsin ((2 : ℝ) ^ (2 * y)) > 0 := by
          apply Real.arcsin_pos.mpr
          all_goals
            try linarith
        linarith
      linarith
    · -- Show that arcsin ((2 : ℝ) ^ (2 * y)) < Real.pi
      have h16 : Real.arcsin ((2 : ℝ) ^ (2 * y)) < Real.pi := by
        have h17 : Real.arcsin ((2 : ℝ) ^ (2 * y)) ≤ Real.pi / 2 := by
          apply Real.arcsin_le_pi_div_two
        have h18 : Real.pi / 2 < Real.pi := by
          linarith [Real.pi_pos]
        linarith
      linarith