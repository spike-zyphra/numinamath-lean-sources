import Mathlib

theorem algebra_159388 (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (h1 : (a + b) / c = d) (h2 : (a + c) / b = d) (h3 : (b + c) / a = d) :
    d = -1 ∨ d = 2 := by
  have eq1 : a + b = c * d := by
    field_simp [hc] at h1
    linarith
  have eq2 : a + c = b * d := by
    field_simp [hb] at h2
    linarith
  have eq3 : b + c = a * d := by
    field_simp [ha] at h3
    linarith
  have h4 : b - c = -(b - c) * d := by
    nlinarith [eq1, eq2]
  have h5 : (b - c) * (1 + d) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case $b - c = 0$, so $b = c$
    have h8 : b = c := by linarith 
    have h4 : a + b = b * d := by
      rw [show c = b by linarith [h8] ] at eq1
      linarith
    have h41 : a = b * (d - 1 : ℝ) := by 
      linarith 
    have h42 : b + c = a * d := eq3
    rw [show c = b by linarith [h8] ] at h42
    rw [h41] at h42 
    have h43 : 2 * b = b * (d - 1) * d := by
      nlinarith 
    have h44 : 2 = (d - 1) * d := by
      apply (mul_left_inj' hb).mp
      linarith 
    have h45 : d ^ 2 - d - 2 = 0 := by
      nlinarith 
    have h46 : (d + 1) * (d - 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h46) with h47 h48
    · -- $d + 1 = 0$
      left 
      linarith 
    · -- $d - 2 = 0$
      right 
      linarith 
  · -- Case $1 + d = 0$, so $d = -1$
    left 
    linarith