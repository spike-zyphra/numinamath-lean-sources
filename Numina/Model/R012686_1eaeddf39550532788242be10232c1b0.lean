import Mathlib

open Real Set

theorem inequalities_289088 (x y z : ℝ) (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1)
    (hz : z ∈ Ioo (-1) 1) (h : x * y + y * z + z * x = 1) :
    6 * ((1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2)) ^ ((1 : ℝ) / 3) ≤
    1 + (x + y + z) ^ 2 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with  ⟨hy1, hy2⟩
  rcases hz with  ⟨hz1, hz2⟩
  have hx3 : 1 - x^2 > 0 := by nlinarith
  have hy3 : 1 - y^2 > 0 := by nlinarith
  have hz3 : 1 - z^2 > 0 := by nlinarith
  have h1 : (1 - x^2) * (1 - y^2) * (1 - z^2) > 0 := by
    positivity
  have h2 : ((1 - x^2) * (1 - y^2) * (1 - z^2)) ^ ((1 : ℝ) / 3) ≤ ( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3 := by
    have h4 : (1 - x^2 : ℝ) ≥ 0 := by linarith
    have h11 : (1 - y^2 : ℝ) ≥ 0 := by linarith
    have h12 : (1 - z^2 : ℝ) ≥ 0 := by linarith
    have h13 : ((1 - x^2) * (1 - y^2) * (1 - z^2)) ^ ((1 : ℝ) / 3) ≤ ( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3 := by
      have h15 : ((1 - x^2) * (1 - y^2) * (1 - z^2)) ≤ (( ( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3 ) ^ 3) := by
        have h16 : ( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3 ≥ 0 := by nlinarith
        nlinarith [sq_nonneg ((1 - x^2) - (1 - y^2)), sq_nonneg ((1 - y^2) - (1 - z^2)), sq_nonneg ((1 - z^2) - (1 - x^2)), 
          mul_nonneg (show 0 ≤ (1 - x^2) by linarith) (show 0 ≤ (1 - y^2) by linarith), 
          mul_nonneg (show 0 ≤ (1 - y^2) by linarith) (show 0 ≤ (1 - z^2) by linarith), 
          mul_nonneg (show 0 ≤ (1 - z^2) by linarith) (show 0 ≤ (1 - x^2) by linarith)
        ]
      have h17 : (( ( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3 ) ^ 3) ^ ((1 : ℝ) / 3) = ( ( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3 ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          positivity
      have h18 : ((1 - x^2) * (1 - y^2) * (1 - z^2)) ^ ((1 : ℝ) / 3) ≤ (( ( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3 ) ^ 3) ^ ((1 : ℝ) / 3) := by
        have h19 : (1 - x^2) * (1 - y^2) * (1 - z^2) ≥ 0 := by positivity
        have h20 : ((1 - x^2) * (1 - y^2) * (1 - z^2)) ≤ (( ( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3 ) ^ 3) := h15
        have h21 : ((1 - x^2) * (1 - y^2) * (1 - z^2)) ^ ((1 : ℝ) / 3) ≤ (( ( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3 ) ^ 3) ^ ((1 : ℝ) / 3) := by
          apply Real.rpow_le_rpow
          all_goals
            try positivity
            try nlinarith
        linarith
      nlinarith [h17, h18]
    linarith
  have h30 : 6 * ((1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2)) ^ ((1 : ℝ) / 3) ≤ 6 * (( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3) := by
    have h31 : ((1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2)) ^ ((1 : ℝ) / 3) ≤ ( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3 := h2
    nlinarith
  have h40 : 6 * (( (1 - x^2) + (1 - y^2) + (1 - z^2) ) / 3) = 6 - 2 * (x^2 + y^2 + z^2) := by
    nlinarith
  have h50 : 6 - 2 * (x^2 + y^2 + z^2) ≤ 1 + (x + y + z) ^ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z)]
  have h60 : 6 * ((1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2)) ^ ((1 : ℝ) / 3) ≤ 1 + (x + y + z) ^ 2 := by
    nlinarith [h30, h40, h50]
  exact h60