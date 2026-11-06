import Mathlib

theorem inequalities_222368 (a b c d : ℝ) (ha : 0 < b) (hb : b < a)
    (hc : 0 < d) (hd : d < c) : a * c > b * d := by
  have ha' : 0 < a := by linarith
  have hc' : 0 < c := by linarith
  have h1 : a - b > 0 := by linarith
  have h2 : c - d > 0 := by linarith
  have h3 : a * (c - d) > 0 := by
    apply mul_pos
    linarith
    linarith
  -- $d(a - b) > 0$ because $d > 0$ and $a - b > 0$
  have h4 : d * (a - b) > 0 := by
    apply mul_pos
    linarith
    linarith
  have h5 : a * c - b * d > 0 := by
    have h6 : a * c - b * d = a * (c - d) + d * (a - b) := by
      linarith
    rw [h6]
    linarith
  linarith