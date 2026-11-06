import Mathlib

theorem algebra_2688 {x : ℝ} (hx : x = √1999 + √2000) :
    1 / (√1999 - √2000) = -x := by
  rw [hx]
  have h1 : (√1999 - √2000) ≠ 0 := by
    have h2 : √1999 < √2000 := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
    have h3 : √1999 - √2000 < 0 := by linarith
    have h4 : √1999 - √2000 ≠ 0 := by
      intro h
      linarith [h3, h]
    exact h4
  field_simp [h1]
  <;> ring_nf <;> norm_num
  <;> ring_nf <;> norm_num