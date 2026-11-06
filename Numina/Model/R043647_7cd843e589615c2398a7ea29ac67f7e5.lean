import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_150974 :
  IsGreatest {s : ℝ | ∃ x y z w : ℝ, (x*y+2*y*z+z*w)/(x^2+y^2+z^2+w^2) = s ∧ ¬(x=0 ∧ y=0 ∧ z=0 ∧ w=0)} ((1 + sqrt 2)/2) := by
  constructor
  · -- Show that (1 + sqrt 2)/2 is indeed attained
    use 1, 1 + Real.sqrt 2, 1 + Real.sqrt 2, 1
    constructor
    · -- Verify that (1 * (1 + sqrt 2) + 2 * (1 + sqrt 2) * (1 + sqrt 2) + (1 + sqrt 2) * 1) / (1^2 + (1 + sqrt 2)^2 + (1 + sqrt 2)^2 + 1^2) = (1 + sqrt 2)/2
      field_simp
      ring_nf
      nlinarith [Real.sqrt_pos.mpr (show 0 < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    · -- Show that ¬(1=0 ∧ 1+sqrt 2=0 ∧ 1+sqrt 2=0 ∧ 1=0)
      intro h
      rcases h with ⟨h1, h2, h3, h4⟩
      norm_num at h1 h2 h3 h4
      all_goals nlinarith [Real.sqrt_pos.mpr (show 0 < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · -- Show that (1 + sqrt 2)/2 is the greatest value
    intro s hs
    rcases hs with ⟨x, y, z, w, heq, hn⟩
    by_contra h
    push_neg at h
    have h1 : x^2 + y^2 + z^2 + w^2 > 0 := by
      by_contra h2
      push_neg at h2
      have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]
      have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]
      have hz : z = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]
      have hw : w = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, sq_nonneg w]
      have h2 : x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := ⟨hx, hy, hz, hw⟩
      contradiction
    have h11 : (x * y + 2 * y * z + z * w) ≤ ((1 + Real.sqrt 2) / 2) * (x^2 + y^2 + z^2 + w^2) := by
      nlinarith [sq_nonneg (x - z), sq_nonneg (y - w), sq_nonneg (x - w), sq_nonneg (y - z),
            sq_nonneg (x + z - y - w), sq_nonneg (x + w - y - z), 
            sq_nonneg (x * Real.sqrt 2 - z), sq_nonneg (y * Real.sqrt 2 - w), 
            sq_nonneg (x - ((1 + Real.sqrt 2) * y)), sq_nonneg (z - ((1 + Real.sqrt 2) * w)),
            sq_nonneg (y - ((1 + Real.sqrt 2) * x)), sq_nonneg (w - ((1 + Real.sqrt 2) * z)),
            sq_nonneg (y - z), sq_nonneg (x - w),
            sq_nonneg (x + w - (y + z)), sq_nonneg (x + w + (y + z)),
            Real.sqrt_nonneg 2, Real.sq_sqrt (show (0: ℝ) ≤ 2 by norm_num)]
    have h3 : (x * y + 2 * y * z + z * w) / (x^2 + y^2 + z^2 + w^2) ≤ (1 + Real.sqrt 2) / 2 := by
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    linarith [h3, heq, h]