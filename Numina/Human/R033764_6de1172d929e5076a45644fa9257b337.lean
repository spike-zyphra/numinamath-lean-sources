import Mathlib

/- 7.3. (Yugoslavia, 76). Prove that if the product of three numbers is 1, and their sum is greater than the sum of their reciprocals, then exactly one of these numbers is greater than 1. -/
theorem algebra_120847 {a b c : ℝ} (hmul : a * b * c = 1) (hsum : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by
  -- wlog assume a is largest
  wlog h : b ≤ a ∧ c ≤ a
    -- if b was largest we could've used the result
  . by_cases h' : a ≤ b ∧ c ≤ b
    . have := this (a := b) (b := a) (c := c) (by linarith) (by linarith) h'
      revert this
      tauto
    . simp at h h'
      -- othewise c was largest, we could've used the result
      have hac : a ≤ c := by
        obtain h'' | h'' := LinearOrder.le_total a b
        . linarith [h' h'']
        . linarith [h h'']
      have hbc : b ≤ c := by
        obtain h'' | h'' := LinearOrder.le_total a b
        . linarith [h' h'']
        . linarith [h h'']
      have := this (a := c) (b := b) (c := a) (by linarith) (by linarith) ⟨hbc, hac⟩
      revert this
      tauto
  -- we'll prove 1 < a and b, c ≤ 1
  left
  obtain ⟨hab, hac⟩ := h
  -- first prove each of a, b, c are nonzero
  have ha : a ≠ 0 := by
    by_contra ha
    simp [ha] at hmul
  have hb : b ≠ 0 := by
    by_contra hb
    simp [hb] at hmul
  have hc : c ≠ 0 := by
    by_contra hc
    simp [hc] at hmul
  -- nowe we can prove (a-1) * (b-1) * (c-1) > 0
  have h : (a - 1) * (b - 1) * (c - 1) = (a * b * c - 1) + (a + b + c) - a * b * c * (1 / a + 1 / b + 1 / c) := by
    ring_nf
    field_simp
    ring
  rw [hmul] at h
  replace h : (a - 1) * (b - 1) * (c - 1) > 0 := by linarith
  -- 1 < a otherwise, b ≤ 1, c ≤ 1 and then (a-1)*(b-1)*(c-1) ≤ 0
  have ha' : 1 < a := by
    by_contra ha'
    simp at ha'
    have hb' : b ≤ 1 := by linarith
    have hc' : c ≤ 1 := by linarith
    have := mul_nonneg_of_nonpos_of_nonpos (show a - 1 ≤ 0 by linarith) (show b - 1 ≤ 0 by linarith)
    have := mul_nonpos_of_nonneg_of_nonpos this (show c - 1 ≤ 0 by linarith)
    linarith
  -- we must have b ≤ 1 otherwise 1 < c and again contradiction
  have hb' : b ≤ 1 := by
    by_contra hb'
    simp at hb'
    have : 0 < (a-1) * (b-1) := mul_pos (show 0 < a - 1 by linarith) (show 0 < b - 1 by linarith)
    have hc' : 0 < c - 1 := (pos_iff_pos_of_mul_pos h).mp this
    have : 1 * 1 * 1 < a * b * c := by gcongr; linarith
    linarith
  -- finally c ≤ 1 or again contradiction
  have hc' : c ≤ 1 := by
    by_contra hc'
    simp at hc'
    have : (a-1) * (b-1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ a - 1 by linarith) (show b - 1 ≤ 0 by linarith)
    have := mul_nonpos_of_nonpos_of_nonneg this (show 0 ≤ c - 1 by linarith)
    linarith
  simp [ha', hb', hc']