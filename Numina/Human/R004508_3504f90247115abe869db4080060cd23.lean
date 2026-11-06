import Mathlib

theorem algebra_276935 (m1 m2 m3 : ℝ) (hm1 : m1 = 150 / 1000) (hm2 : m2 = 1 / 1000)
    (hm3 : m3 = 30 / 1000) (V : ℝ) (hV : V = 10) :
    let v1 := (2 * m1 + m3) / (m1 + m2 + m3) * V
    let v3 := (2 * m3 + m2) / (m1 + m2 + m3) * V
    v1 > 0 ∧ v3 > 0 := by subst_vars; norm_num