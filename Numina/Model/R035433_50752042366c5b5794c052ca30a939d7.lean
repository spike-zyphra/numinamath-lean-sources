import Mathlib

theorem algebra_130467 {b : ℕ → ℝ} (hb : ∃ r, ∀ n, b n = b 0 * r ^ n)
    (hpos : ∀ n, b n > 0) (hinc : ∀ n, b n < b (n + 1)) (h4 : b 4 + b 3 - b 2 - b 1 = 5) :
    b 6 + b 5 ≥ 20 := by 
  rcases hb with ⟨r, hr⟩
  have b0_pos : b 0 > 0 := by
    specialize hpos 0
    simpa using hpos
  have r_pos : r > 0 := by
    have h1_pos : b 1 > 0 := hpos 1
    rw [hr 1] at h1_pos
    nlinarith [b0_pos, h1_pos]
  have r1 : r > 1 := by
    have h01 : b 0 < b 1 := hinc 0
    rw [hr 0] at h01
    rw [hr 1] at h01
    nlinarith [b0_pos, r_pos]
  have eq1 : b 4 + b 3 - b 2 - b 1 = 5 := by linarith
  have eq2 : b 4 = b 0 * r ^ 4 := hr 4
  have eq3 : b 3 = b 0 * r ^ 3 := hr 3
  have eq4 : b 2 = b 0 * r ^ 2 := hr 2
  have eq5 : b 1 = b 0 * r ^ 1 := hr 1
  rw [eq2, eq3, eq4, eq5] at eq1
  have eq6 : b 6 = b 0 * r ^ 6 := hr 6
  have eq7 : b 5 = b 0 * r ^ 5 := hr 5
  rw [eq6, eq7]
  nlinarith [sq_nonneg (r ^ 2 - 2), sq_nonneg (r ^ 2 - 1), sq_nonneg (b 0 * r ^ 2), sq_nonneg (b 0 * (r ^ 2 - 1)), sq_nonneg (r * (r - 1)), sq_pos_of_pos b0_pos, sq_pos_of_pos r_pos, sq_pos_of_pos (show r ^ 2 > 0 by positivity), sq_nonneg (r - 1), sq_pos_of_pos (show r > 0 by linarith [r_pos] ), mul_pos b0_pos r_pos, mul_pos b0_pos (show r ^ 2 > 0 by positivity), mul_pos r_pos (show r ^ 2 > 0 by positivity) ]