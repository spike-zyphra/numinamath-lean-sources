import Mathlib

/- If $\left(a+\frac{1}{a}\right)^{2}=3$, find $\left(a+\frac{1}{a}\right)^{3}$ in terms of $a$.-/
theorem algebra_610930 (a : ℝ) (ha : a ≠ 0) (h : (a + 1 / a) ^ 2 = 3) : (a + 1 / a) ^ 3 = 0 := by
  -- We have a² + 1 / a² = 1.
  have h₁ : a ^ 2 + (1 / a) ^ 2 = 1 := by
    rw [add_sq, mul_assoc, mul_one_div, div_self ha] at h
    linarith
  -- We have (a² + 1 / a²)(a + 1 / a) = a + 1 / a.
  have h₂ : (a ^ 2 + (1 / a) ^ 2) * (a + 1 / a) = a + 1 / a := by
    rw [h₁, one_mul]
  -- We have a³ + 1 / a³ = 0.
  have h₃ : a ^ 3 + (1 / a) ^ 3 = 0 := by
    rw [show a ^ 3 + (1 / a) ^ 3 = (a + 1 / a) * (a ^ 2 + (1 / a) ^ 2 - a * (1 / a)) from by ring_nf, mul_sub, mul_comm, h₂]
    field_simp
  -- Rearranging and we get a = -1 / a.
  have h₄ : a = -1 / a := by
    apply eq_sub_of_add_eq at h₃
    rw [div_pow] at h₃
    simp [-one_div] at h₃
    rw [<-neg_div, eq_div_iff_mul_eq, <-mul_pow, show (-1 : ℝ) = (-1) ^ 3 by norm_num, pow_eq_pow_iff_cases] at h₃
    norm_num [show ¬Even 3 by tauto] at h₃
    rw [eq_div_iff_mul_eq, h₃]
    exact ha
    simp [ha]
  -- We have (a + 1 / a)³ = 0.
  nth_rw 1 [h₄]
  ring