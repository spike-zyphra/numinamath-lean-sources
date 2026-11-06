import Mathlib

theorem inequalities_602509 (a b c x y z k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 0 < k) (h1 : a + x = k) (h2 : b + y = k)
    (h3 : c + z = k) : a * y + b * z + c * x < k ^ 2 := by

  have hx_eq : x = k - a := by linarith
  have hy_eq : y = k - b := by linarith
  have hz_eq : z = k - c := by linarith

  rw [hx_eq, hy_eq, hz_eq]

  have hk1 : k > a := by nlinarith
  have hk2 : k > b := by nlinarith
  have hk3 : k > c := by nlinarith

  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha (show 0 < k - a by nlinarith),
      mul_pos hb hc, mul_pos hb (show 0 < k - b by nlinarith), mul_pos hc (show 0 < k - c by nlinarith),
      mul_pos (show 0 < k - a by nlinarith) (show 0 < k - b by nlinarith), mul_pos (show 0 < k - a by nlinarith) (show 0 < k - c by nlinarith), mul_pos (show 0 < k - b by nlinarith) (show 0 < k - c by nlinarith),
      sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos (show 0 < k - a by nlinarith), sq_pos_of_pos (show 0 < k - b by nlinarith), sq_pos_of_pos (show 0 < k - c by nlinarith)
  ]