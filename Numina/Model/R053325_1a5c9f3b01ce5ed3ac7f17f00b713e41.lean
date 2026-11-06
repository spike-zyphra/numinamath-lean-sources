import Mathlib

theorem algebra_276880 {m1 m2 m3 V : ℝ} (hm1 : m1 = 150 / 1000) (hm2 : m2 = 30 / 1000)
    (hm3 : m3 = 1 / 1000) (hV : V = 10) :
    let v1 := (2 * m1 + m2 + m3) * V / (m1 + m2 + m3)
    let v3 := (2 * m1 + m2 + m3 - 2 * m2) * V / (m1 + m2 + m3 - 2 * m2)
    v1 > 0 ∧ v3 > 0 := by
  simp only [hm1, hm2, hm3, hV]
  norm_num