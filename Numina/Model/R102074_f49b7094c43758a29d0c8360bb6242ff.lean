import Mathlib

theorem inequalities_312783 (a b c d x y z m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hm : 0 < m)
    (h1 : a + x = 1) (h2 : b + y = 1) (h3 : c + z = 1) (h4 : d + m = 1) :
    a * m + b * x + c * y + d * z < 2 := by 
  have hx1 : x = 1 - a := by linarith
  have hy1 : y = 1 - b := by linarith
  have hz1 : z = 1 - c := by linarith
  have hm1 : m = 1 - d := by linarith
  rw [hx1, hy1, hz1, hm1]
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos ha hx, mul_pos ha hy, mul_pos ha hz, mul_pos ha hm,
          mul_pos hb hc, mul_pos hb hd, mul_pos hb hx, mul_pos hb hy, mul_pos hb hz, mul_pos hb hm,
          mul_pos hc hd, mul_pos hc hx, mul_pos hc hy, mul_pos hc hz, mul_pos hc hm,
          mul_pos hd hx, mul_pos hd hy, mul_pos hd hz, mul_pos hd hm,
          mul_pos hx hy, mul_pos hx hz, mul_pos hx hm,
          mul_pos hy hz, mul_pos hy hm,
          mul_pos hz hm]