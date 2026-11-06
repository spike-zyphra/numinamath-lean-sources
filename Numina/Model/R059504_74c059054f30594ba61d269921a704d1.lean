import Mathlib

theorem algebra_130670 {a b : ℝ} (hb : b ≠ 0) (h1 : a + b = a * b) (h2 : a * b = a / b) :
    a = 1 / 2 ∧ b = -1 := by
  have eq1 : a * b * b = a := by 
    field_simp [hb] at h2 
    linarith 
  have eq2 : a * (b^2 - 1) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp eq2) with ha1 ha2
  · -- Consider case where $a = 0$
    have habs : b = 0 := by
      rw [ha1] at h1
      linarith
    contradiction
  · -- Case where $b^2 - 1 = 0$, so $b^2 = 1$, hence $b = 1$ or $b = -1$
    have hb_eq : b^2 = 1 := by
      linarith
    have getb : b = 1 ∨ b = -1 := by 
      rw [sq_eq_one_iff] at hb_eq
      exact hb_eq
    rcases getb with h4 | h4
    · -- Consider case where $b = 1$: From h1 = a+1 = a*1 = a: contradiction
      rw [show b = 1 by linarith [h4] ] at h1 
      nlinarith
    · -- Hence we must have b = -1
      have ha5 : a = 1 / 2 := by 
        rw [show b = -1 by linarith [h4] ] at h1
        linarith
      constructor
      · exact ha5
      · linarith