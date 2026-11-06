import Mathlib

theorem algebra_147166 {a b : ℝ} (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ 2018*x1^2+a*x1+b=0 ∧ 2018*x2^2+a*x2+b=0 ∧ ∃ n : ℤ, x1-x2=n) :
    2018^2 ∣ a^2-4*2018*b := by
  rcases h with ⟨x1, x2, hx12, h1, h2, ⟨n, hn⟩⟩
  have h_sub : 2018 * (x1^2 - x2^2) + a * (x1 - x2) = 0 := by
    nlinarith
  have h_sum : 2018 * (x1 + x2) + a = 0 := by
    apply (mul_left_inj' (show x1 - x2 ≠ 0 by
      intro h_eq 
      apply hx12 
      linarith 
    )).mp
    nlinarith [h_sub]
  have h_x1x2 : x1 + x2 = -a / 2018 := by
    nlinarith
  have h_prod : x1 * x2 = b / 2018 := by
    nlinarith [sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by
      intro h_eq 
      apply hx12 
      linarith 
    ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), h_x1x2]
  have h_eq : (x1 - x2) ^ 2 = (x1 + x2) ^ 2 - 4 * (x1 * x2) := by
    nlinarith
  rw [show x1 - x2 = (↑n : ℝ) by linarith [hn]] at h_eq
  rw [h_x1x2, h_prod] at h_eq
  have h_eq2 : (↑n : ℝ) ^ 2 * (2018 ^ 2 : ℝ) = a ^ 2 - 4 * 2018 * b := by
    nlinarith [h_eq]
  use n ^ 2
  norm_num at h_eq2 ⊢
  nlinarith [h_eq2]