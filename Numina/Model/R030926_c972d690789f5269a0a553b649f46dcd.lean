import Mathlib

theorem algebra_47548 {a b c : ℝ} (ha : a ≠ -b) (hb : b ≠ -c) (hc : a ≠ -c)
    (h : b^2 - a^2 = c^2 - b^2) :
    1 / (b + c) - 1 / (c + a) = 1 / (c + a) - 1 / (a + b) := by

  have h1 : a + b ≠ 0 := by
    intro h'
    apply ha
    linarith

  have h2 : b + c ≠ 0 := by
    intro h'
    apply hb
    linarith

  have h3 : c + a ≠ 0 := by
    intro h'
    apply hc
    linarith

  have eq1 : 1 / (b + c) - 1 / (c + a) = ( (a + b) * (a - b) ) / ( (b + c) * (c + a) * (a + b) ) := by
    field_simp [(show b + c ≠ 0 by exact h2), (show c + a ≠ 0 by exact h3), (show a + b ≠ 0 by exact h1)]
    ring

  have eq2 : 1 / (c + a) - 1 / (a + b) = ( (b + c) * (b - c) ) / ( (b + c) * (c + a) * (a + b) ) := by
    field_simp [(show c + a ≠ 0 by exact h3), (show a + b ≠ 0 by exact h1), (show b + c ≠ 0 by exact h2)]
    ring

  rw [eq1, eq2]

  have eq3 : (a + b) * (a - b) = (b + c) * (b - c) := by
    nlinarith

  rw [show ( (a + b) * (a - b) ) = ( (b + c) * (b - c) ) by linarith [eq3] ]
  <;> norm_num
  <;> ring_nf
  <;> norm_num