import Mathlib

theorem inequalities_65897 (p q r : ℝ) (n : ℕ) (hpqr : p > 0 ∧ q > 0 ∧ r > 0)
    (h : p * q * r = 1) :
    1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) +
    1 / (r ^ n + p ^ n + 1) ≤ 1 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have h1 : p ^ n > 0 := by positivity
  have h2 : q ^ n > 0 := by positivity
  have h3 : r ^ n > 0 := by positivity
  have h4 : p ^ n * q ^ n * r ^ n = 1 := by
    have h' : p ^ n * q ^ n * r ^ n = (p * q * r) ^ n := by
      ring_nf
    rw [h'] at *
    rw [h] at *
    all_goals norm_num
  have h5 : 1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) + 1 / (r ^ n + p ^ n + 1) - 1 ≤ 0 := by
    have h7 : 1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) + 1 / (r ^ n + p ^ n + 1) - 1 =
        ((q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) - (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1)) / ((p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1)) := by 
      field_simp
      ring
    rw [h7] at *
    have h8 : (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) > 0 := by positivity
    have h9 : (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) - (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) ≤ 0 := by
      set x := p ^ n with hx
      set y := q ^ n with hy
      set z := r ^ n with hz 
      clear hx hy hz
      have h6 : x > 0 := by positivity
      have h7 : y > 0 := by positivity
      have h8 : z > 0 := by positivity
      have h9 : x * y * z = 1 := by 
        have hsm := h4
        simp at hsm
        linarith
      have f1 : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
      have f2 : (y - z) ^ 2 ≥ 0 := sq_nonneg (y - z)
      have f3 : (z - x) ^ 2 ≥ 0 := sq_nonneg (z - x)
      have f4 : (x * y - 1) ^ 2 ≥ 0 := sq_nonneg (x * y - 1)
      have f5 : (y * z - 1) ^ 2 ≥ 0 := sq_nonneg (y * z - 1)
      have f6 : (z * x - 1) ^ 2 ≥ 0 := sq_nonneg (z * x - 1)
      nlinarith [mul_pos h6 h7, mul_pos h7 h8, mul_pos h8 h6, mul_pos (show 0 < x by linarith [h6]) (show 0 < y by linarith [h7]), mul_pos (show 0 < y by linarith [h7]) (show 0 < z by linarith [h8]), mul_pos (show 0 < z by linarith [h8]) (show 0 < x by linarith [h6]), h9]
    -- apply (div_le_iff₀ (by positivity)).mpr 
    apply div_nonpos_of_nonpos_of_nonneg 
    linarith 
    all_goals positivity
  linarith