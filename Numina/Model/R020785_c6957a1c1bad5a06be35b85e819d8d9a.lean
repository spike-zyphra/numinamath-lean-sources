import Mathlib

theorem algebra_289352 (a b : ℝ) (ha : a^4-7*a-3=0) (hb : b^4-7*b-3=0) (h : a>b) :
    (a-b)/(a^4-b^4) = 1/7 := by

  have h1 : a^4 - b^4 = 7 * (a - b) := by
    nlinarith [hb, ha]
  have h2 : a - b ≠ 0 := by
    nlinarith
  have h3 : (a - b) / (a^4 - b^4) = (a - b) / (7 * (a - b)) := by
    rw [h1]
  rw [h3]
  have h4 : (a - b) / (7 * (a - b)) = 1 / 7 := by
    have hbne : a - b ≠ 0 := h2
    field_simp [hbne]
    <;> ring_nf <;> norm_num
  exact h4