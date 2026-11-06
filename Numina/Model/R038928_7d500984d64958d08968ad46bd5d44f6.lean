import Mathlib

theorem algebra_302498 {x y z : ℝ} (h1 : 2*(x+y+z)-5*Real.sqrt (x+y+z+5)=2)
    (h2 : x/3=y/4) (h3 : y/4=z/5) :
    x=11/4 ∧ y=11/3 ∧ z=55/12 := by

  have h4 : y = 4/3 * x := by
    linarith

  have h5 : z = 5/3 * x := by
    have h6 : y / 4 = z / 5 := by linarith
    rw [show y / 4 = (4 / 3 * x) / 4 by nlinarith [h4] ] at h6
    linarith

  have h7 : x + y + z = 4 * x := by
    rw [h4, h5]
    linarith

  have h8 : 2 * (x + y + z) - 5 * Real.sqrt (x + y + z + 5) = 2 := h1
  rw [h7] at h8
  have h9 : 8 * x - 5 * Real.sqrt (4 * x + 5) = 2 := by
    ring_nf at h8 ⊢
    nlinarith

  by_cases h10 : 4 * x + 5 ≥ 0
  · -- Assume 4 * x + 5 ≥ 0
    have h11 : Real.sqrt (4 * x + 5) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h9a : 8 * x - 2 = 5 * Real.sqrt (4 * x + 5) := by linarith
    have h12 : Real.sqrt (4 * x + 5) = (8 * x - 2) / 5 := by
      nlinarith
    have h13 : (8 * x - 2) / 5 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg (4 * x + 5), h12]
    have h14 : ((8 * x - 2) / 5) ^ 2 = 4 * x + 5 := by
      calc
        ((8 * x - 2) / 5) ^ 2 = (Real.sqrt (4 * x + 5)) ^ 2 := by
          rw [h12]
        _ = 4 * x + 5 := by
          rw [Real.sq_sqrt]
          linarith
    -- Now implement substitution
    have h15 : 64 * x ^ 2 - 132 * x - 121 = 0 := by
      nlinarith
    have h16 : (x - 11 / 4) * (x + 11 / 16) = 0 := by nlinarith
    cases' (mul_eq_zero.1 h16) with h17 h18
    · -- x - 11/4 = 0
      have hx : x = 11 / 4 := by linarith
      have hy : y = 11 / 3 := by
        linarith [h4, hx]
      have hz : z = 55 / 12 := by
        linarith [h5, hx]
      exact ⟨hx, hy, hz⟩
    · -- x + 11/16 = 0
      have hx : x = -11 / 16 := by linarith
      nlinarith [Real.sqrt_nonneg (4 * x + 5), h12, h9a]
  · -- Assume 4 * x + 5 < 0
    have h14 : 4 * x + 5 < 0 := by linarith
    have h15 : Real.sqrt (4 * x + 5) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      nlinarith
    nlinarith [Real.sqrt_nonneg (4 * x + 5)]