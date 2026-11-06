import Mathlib

open Real Set

/- 9. It is given that $x$ and $y$ are two real numbers such that $x>1$ and $y>1$. Find the smallest possible value of
$$\frac{\log _{x} 2011+\log _{y} 2011}{\log _{x y} 2011} .$$
(A) 4
(B) 6
(C) 8
(D) 10
(E) 12 -/

theorem algebra_100084 :
    IsLeast {z : ℝ | ∃ x y, x > 1 ∧ y > 1 ∧ z = (logb x 2011 + logb y 2011) / logb (x * y) 2011} 4 := by
    unfold IsLeast
    constructor
    --4 fulfills the condition 4 = (logb x 2011 + logb y 2011) / logb (x * y) 2011, for some x and y
    · simp
      --the above equality holds true when x = y = 2011
      use 2011
      constructor
      · linarith
      · use 2011
        constructor
        · linarith
        · have h: logb (2011 * 2011) 2011 ≠ 0 := by norm_num
          field_simp [h]
          rw [Eq.symm (logb_rpow_eq_mul_logb_of_pos (by norm_num))]
          apply (logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)).mpr
          ring
    --4 is the smallest number in the set
    · unfold lowerBounds
      simp
      intro a x hx y hy h
      rw [h]
      --by explicit calculations
      calc
        --(logb x 2011 + logb y 2011) / logb (x * y) 2011 = (log 2011 / log x + (log 2011 / log y)) * (log (x * y) / log 2011)
        (logb x 2011 + logb y 2011) / logb (x * y) 2011 = (log 2011 / log x + (log 2011 / log y)) * (log (x * y) / log 2011) := by
          rw [log_mul (by linarith) (by linarith)]
          repeat rw [← log_div_log]
          field_simp [log_ne_zero.2]
          left
          rw [log_mul (by linarith) (by linarith)]
        --(log 2011 / log x + (log 2011 / log y)) * (log (x * y) / log 2011) = (1 / log x + 1 / log y) * (log x + log y)
        _ = (1 / log x + 1 / log y) * (log x + log y) := by
          rw [log_mul (by linarith) (by linarith)]
          field_simp [log_ne_zero.2]
          ring
        -- (1 / log x + 1 / log y) * (log x + log y) = 2 + log x / log y + log y / log x
        _ = 2 + log x / log y + log y / log x := by
          rw [RightDistribClass.right_distrib]
          repeat rw [LeftDistribClass.left_distrib]
          repeat rw [div_mul_eq_mul_div, one_mul]
          repeat rw [div_self (by apply log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith))]
          ring
        -- 2 + log x / log y + log y / log x ≥ 4
        _ ≥ 4 := by
          --by AM/GM inequality we get the desired result
          have h_mean : (log x / log y) ^ ((1 : ℝ)/2) * (log y / log x) ^ ((1 : ℝ)/2) ≤ ((1 : ℝ)/2) * (log x / log y) + ((1 : ℝ)/2) * (log y / log x) := by
            exact geom_mean_le_arith_mean2_weighted (by linarith) (by linarith) (div_nonneg (log_nonneg (by linarith)) (log_nonneg (by linarith))) (div_nonneg (log_nonneg (by linarith)) (log_nonneg (by linarith))) (by linarith)
          rw [← mul_rpow (div_nonneg (log_nonneg (by linarith)) (log_nonneg (by linarith))) (div_nonneg (log_nonneg (by linarith)) (log_nonneg (by linarith)))] at h_mean
          rw [← mul_add] at h_mean
          field_simp [log_ne_zero.2] at h_mean
          rw [mul_comm, div_self (mul_ne_zero (log_ne_zero.2 ⟨by linarith, by linarith, by linarith⟩) (log_ne_zero.2 ⟨by linarith, by linarith, by linarith⟩))] at h_mean
          simp at h_mean
          have h2_mean : 2 ≤ (log x / log y + log y / log x) := by linarith
          linarith