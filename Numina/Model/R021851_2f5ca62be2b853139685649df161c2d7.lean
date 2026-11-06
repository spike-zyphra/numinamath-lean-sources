import Mathlib

theorem inequalities_318406 (p q r : ℝ) (hpqr : p > 0 ∧ q > 0 ∧ r > 0)
    (h : p * q * r = 1) (n : ℕ) :
    1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) +
    1 / (r ^ n + p ^ n + 1) ≤ 1 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have h1 : p ^ n > 0 := by positivity
  have h2 : q ^ n > 0 := by positivity
  have h3 : r ^ n > 0 := by positivity
  have hpq : p ^ n * q ^ n * r ^ n = 1 := by
    calc
        p ^ n * q ^ n * r ^ n
          = (p * q * r) ^ n := by
            rw [mul_pow, mul_pow]
        _ = 1 ^ n := by rw [h]
        _ = 1 := by
          simp
  have h5 : p ^ n + q ^ n + 1 > 0 := by positivity
  have h6 : q ^ n + r ^ n + 1 > 0 := by positivity
  have h7 : r ^ n + p ^ n + 1 > 0 := by positivity
  have h9 : 1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) + 1 / (r ^ n + p ^ n + 1) - 1 ≤ 0 := by
    have hpq1 : p ^ n * q ^ n * r ^ n = 1 := hpq
    have h11 : 0 < p ^ n * q ^ n := by positivity
    have h12 : 0 < p ^ n * r ^ n := by positivity
    have h13 : 0 < q ^ n * r ^ n := by positivity
    have h8 : 0 < p ^ n := by positivity
    have h9 : 0 < q ^ n := by positivity
    have h10 : 0 < r ^ n := by positivity
    have h5 : 0 < p ^ n * q ^ n * r ^ n := by positivity
    have hpn_pos : p ^ n > 0 := by positivity
    have hqn_pos : q ^ n > 0 := by positivity
    have hrn_pos : r ^ n > 0 := by positivity
    have h4 : p ^ n * q ^ n * r ^ n = 1 := hpq
    have h5_1 : 0 < p ^ n * q ^ n := by positivity
    have h5_2 : 0 < p ^ n * r ^ n := by positivity
    have h5_3 : 0 < q ^ n * r ^ n := by positivity
    have h50 : 0 < p ^ n * q ^ n * r ^ n := by positivity
    have h12 : (1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) + 1 / (r ^ n + p ^ n + 1) - 1) =
      ( (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) - (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) ) / ((p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1)) := by
      field_simp
      <;> ring
    rw [h12] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is nonpositive
      have h14 : (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) - (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) ≤ 0 := by 
        nlinarith [sq_nonneg (p ^ n - 1), sq_nonneg (q ^ n - 1), sq_nonneg (r ^ n - 1), 
            sq_nonneg (p ^ n * q ^ n - 1), sq_nonneg (p ^ n * r ^ n - 1), sq_nonneg (q ^ n * r ^ n - 1), 
            h4, mul_pos hpn_pos hqn_pos, 
            mul_pos hqn_pos hrn_pos, 
            mul_pos hpn_pos hrn_pos
          ]
      linarith
    · -- Show that the denominator is nonnegative
      positivity
  linarith [h9]