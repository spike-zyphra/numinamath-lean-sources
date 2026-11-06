import Mathlib

open Real Set
open scoped BigOperators

/- Example 3. Solve the inequality


$$

x \log _{1 / 10}\left(x^{2}+x+1\right)>0

$$
 -/
theorem inequalities_254392 (x : ℝ) :
  x * logb (1 / 10) (x^2 + x + 1) > 0 ↔ x < -1 := by
  constructor
  · intro h
    -- we remove the division in log base
    rw [Real.logb_div_base (by norm_num) (by norm_num), Real.logb_one_left] at h
    conv_lhs at h =>
      calc _
      _ = -x * ((logb 10 (x ^ 2 + x + 1))⁻¹)⁻¹ := by ring_nf
      _ = -x * logb 10 (x ^ 2 + x + 1) := by simp
    -- split by cases for x >< 0
    cases' lt_trichotomy 0 x with h1 h1
    · suffices 0 < -x * logb 10 (x ^ 2 + x + 1) by
        apply mul_pos_iff.mp at h
        cases' h with h' h'
        · obtain ⟨h1, h2⟩ := h'
          simp at h1; linarith
        · obtain ⟨h1, h2⟩ := h'
          rw [Real.logb_neg_iff] at h2
          nlinarith
          norm_num
          nlinarith
      linarith
    cases' h1 with h1 h1
    · rw [← h1] at h; simp at h
    · apply mul_pos_iff.mp at h
      cases' h with h' h'
      rotate_left
      · obtain ⟨h1, h2⟩ := h'
        simp at h1; linarith
      · obtain ⟨h1, h2⟩ := h'
        rw [Real.logb_pos_iff] at h2
        nlinarith
        norm_num
        nlinarith
  -- now for the other direction
  intro h
  simp
  apply mul_pos_iff.mpr
  right
  constructor
  linarith
  ring_nf
  -- we again get rif od the 1/10 in the base
  rw [Real.logb_div_base (by norm_num) (by norm_num), Real.logb_one_left]
  simp
  refine (Real.logb_pos_iff ?_ ?_).mpr ?_
  simp
  nlinarith
  nlinarith