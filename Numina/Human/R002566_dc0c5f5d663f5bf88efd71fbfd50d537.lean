import Mathlib.Tactic

-- On a trip from the United States to Canada, Isabella took $d$ U.S. dollars. At the border she exchanged them all, receiving $10$ Canadian dollars for every $7$ U.S. dollars. After spending $60$ Canadian dollars, she had $d$ Canadian dollars left. What is the sum of the digits of $d$?
-- $\mathrm{(A)\ }5\qquad\mathrm{(B)\ }6\qquad\mathrm{(C)\ }7\qquad\mathrm{(D)\ }8\qquad\mathrm{(E)\ }9$

-- first we define a function to calculate the sum of digits of a given number
def digitSum (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n + 1 => (n + 1) % 10 + digitSum ((n + 1) / 10)

-- now the main problem
theorem alg_1152
  (d : ℕ)
  (h_CAD : d * (10/7 : ℝ) = 60 + d) :
  digitSum (d : ℕ) = 5 := by
    -- multiply both sides by 7
    have d_10 : 10 * (d : ℝ) = 420 + 7 * d := by
      have ten_div_7_mul_7 : (10 / 7 : ℝ ) * 7  = 10 := by
       refine div_mul_cancel₀ 10 ?h
       exact Ne.symm (OfNat.zero_ne_ofNat 7)
      have ten_d : d * (10/7 : ℝ) * 7 = 10 * d := by
        rw [mul_assoc, ten_div_7_mul_7, mul_comm]
      have ten_d_eq_60_p_7_d : 10 * (d : ℝ) = (60 + d) * 7 := by
        exact Eq.symm (Mathlib.Tactic.Ring.mul_congr (id (Eq.symm h_CAD)) rfl ten_d)
      aesop
      ring
    -- solve the equation for finding d
    have d_final : d = 140 := by
      have ten_minus_7 : 10 * (d : ℝ) - 7 * d = 420 := by exact sub_eq_iff_eq_add.mpr d_10
      have ten_minus_3_eq_7d : 10 * (d : ℝ) - 7 * d = 3 * d := by ring
      have three_d : 3 * (d : ℝ) = 420 := by rw [← ten_minus_3_eq_7d, ten_minus_7]
      have : (d : ℝ) = 420 / 3 := by
       refine EuclideanDomain.eq_div_of_mul_eq_right ?ha three_d; simp
      norm_num at this
      exact Nat.cast_inj.mp this
    -- we have d, now use the digitSum function to calculate sum of digits of d
    rw [d_final]
    unfold digitSum
    simp
    unfold digitSum
    simp
    unfold digitSum
    simp
    unfold digitSum
    simp