import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_179327 {x y : ℝ} (hx : x ∈ Ioo (-2) 2) (hy : y ∈ Ioo (-2) 2)
  (hxy : x * y = -1) :
  4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) ≥ 12 / 5 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : 4 - x^2 > 0 := by 
    nlinarith [sq_nonneg x]
  have h2 : 9 - y^2 > 0 := by 
    nlinarith [sq_nonneg y]
  have h3 : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5 ≥ 0 := by
    have h4 : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) - 12 / 5 =
        (20 * (9 - y^2) + 45 * (4 - x^2) - 12 * ((4 - x^2) * (9 - y^2)) ) / ((4 - x^2) * (9 - y^2) * 5) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    -- We need to show the numerator is non-negative
    have hx3 : x^2 > 0 := by 
      nlinarith
    have h5 : 20 * (9 - y ^ 2) + 45 * (4 - x ^ 2) - 12 * ((4 - x ^ 2) * (9 - y ^ 2)) ≥ 0 := by 
      have hx3' : x^2 > 0 := hx3
      have hy3' : y^2 > 0 := by
        nlinarith [show x ≠ 0 from by nlinarith, hxy]
      have h6 : x^2 * y^2 = 1 := by 
        have h7 : x * y = -1 := hxy
        calc 
          x^2 * y^2 = (x * y) ^ 2 := by ring
          _ = (-1) ^ 2 := by rw [h7]
          _ = 1 := by norm_num 
      have h5' : 20 * (9 - y ^ 2) + 45 * (4 - x^2) - 12 * ((4 - x^2) * (9 - y^2)) = 7 * (9 * x^2 + 4 / x^2 - 12) := by 
        have hx4 : y^2 = 1 / x^2 := by 
          field_simp [(show x ≠ 0 from by nlinarith)]
          nlinarith [h6]
        rw [show y ^2 = 1 / x^2 by linarith [hx4]]
        field_simp [(show x ≠ 0 from by nlinarith)]
        <;> nlinarith [h6, sq_nonneg (x^2 - 1 / 3), sq_nonneg (y^2 - 1 / 3)]
      rw [h5']
      have hx5 : 9 * x ^2 + 4 / x ^2 ≥ 12 := by 
        have hx6 : x^2 > 0 := hx3'
        have h9 : 9 * x^4 + 4 ≥ 12 * x^2 := by 
          have h10 : (3 * x^2 - 2) ^ 2 ≥ 0 := sq_nonneg (3 * x^2 - 2)
          nlinarith [h10, sq_nonneg x]
        have hx8 : x ^2 > 0 := hx3'
        have h9' : 9 * x^2 + 4 / x^2 ≥ 12 := by 
          have h11 : (9 * x ^2 + 4 / x ^2) = (9 * x^4 + 4) / x^2 := by 
            field_simp [(show x ≠ 0 from by nlinarith)]
            <;> ring
          rw [h11]
          apply (le_div_iff₀ (by positivity)).mpr 
          nlinarith 
        linarith 
      nlinarith 
    linarith 
    all_goals 
      have h5' : (4 - x ^ 2) * (9 - y ^ 2) * 5 > 0 := by 
        positivity 
      linarith 
  linarith [h3]