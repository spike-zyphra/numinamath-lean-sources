import Mathlib

set_option linter.unusedVariables false
theorem algebra_265308 {x a b m n : ℝ} (hx : x = a * m + b * n) (h : (x + m) ^ 2 - (x + n) ^ 2 = (m - n) ^ 2) (hmn : m ≠ n) (hm : m ≠ 0) (hn : n ≠ 0) : (a = 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = 0) := by
  rw [hx] at h
  have eq1 : (m - n) * (2 * (a * m + b * n) + m + n) = (m - n) * (m - n) := by
    nlinarith
  have h1 : m - n ≠ 0 := by
    intro h2
    apply hmn
    linarith
  have eq2 : 2 * (a * m + b * n) + m + n = m - n := by
    apply (mul_left_inj' h1).mp
    linarith
  have eq3 : a * m + (b + 1) * n = 0 := by
    linarith
  by_cases ha : a = 0
  · -- a = 0
    have hb1 : (b + 1) * n = 0 := by
      rw [ha] at eq3
      linarith
    have hb2 : b + 1 = 0 := by
      apply (mul_left_inj' hn).mp
      linarith
    have hb3 : b ≠ 0 := by
      intro hb4
      have : b = 0 := by linarith
      rw [this] at hb2
      norm_num at hb2
    left
    exact ⟨ha, hb3⟩
  · -- a ≠ 0
    by_cases hb : b = 0
    · -- b = 0
      have eq4 : a * m + n = 0 := by
        rw [hb] at eq3
        linarith
      have ha2 : a ≠ 0 := by
        intro ha0
        rw [ha0] at eq4
        have : n = 0 := by nlinarith
        contradiction
      right
      right
      exact ⟨ha2, hb⟩
    · -- b ≠ 0
      have hb2 : b ≠ 0 := hb
      have ha2 : a ≠ 0 := by
        intro ha0
        tauto
      right
      left
      exact ⟨ha2, hb2⟩