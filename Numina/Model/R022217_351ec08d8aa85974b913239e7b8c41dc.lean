import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_20398 {l w : ℝ} (hl : l > 0) (hw : w > 0)
  (h : 2*l + 2*π*w/2 = 400) :
  l * w ≤ 20000 / π := by
  have h1 : 2 * l + π * w = 400 := by
    nlinarith [h, Real.pi_pos]

  have h2 : l = (400 - π * w) / 2 := by
    linarith

  have h3 : l * w = (400 * w - π * w ^ 2) / 2 := by
    rw [h2]
    nlinarith [Real.pi_pos]

  have h4 : π > 0 := Real.pi_pos

  have h50 : π * (400 * w - π * w ^ 2) ≤ 40000 := by
    nlinarith [sq_nonneg (w - 200 / π), sq_nonneg (w * π - 200), sq_nonneg ((400 - π * w)/2 - 100), 
      sq_nonneg ((π) - 3), sq_nonneg (w * π - 200), mul_pos (show 0 < π by linarith [Real.pi_pos]) (show 0 < π by linarith [Real.pi_pos]), sq_nonneg ((w) - 200 / π) ]

  have h4' : (400 * w - π * w ^ 2) / 2 ≤ 20000 / π := by
    have h6 : (400 * w - π * w ^ 2) / 2 ≤ 20000 / π := by
      have h7 : π > 0 := h4
      have h8 : π * (400 * w - π * w ^ 2) ≤ 40000 := h50
      have h6' : (400 * w - π * w^2) / 2 ≤ (20000 / π) := by
        have h9 : π > 0 := h4
        have h12 : (400 * w - π * w^2) / 2 ≤ (20000 / π) := by
          have h13 : π > 0 := h4
          have h54 : (π * (400 * w - π * w ^ 2) ) <= (40000: ℝ) := by 
            linarith [h50]
          have h14 : π > 0 := h4
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith [h50, h4]
        linarith
      linarith
    linarith

  have h5 : l * w ≤ 20000 / π := by
    linarith [h3, h4']

  exact_mod_cast h5