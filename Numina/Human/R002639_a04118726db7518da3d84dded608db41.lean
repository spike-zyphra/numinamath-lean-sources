import Mathlib
open Real

/- The number $$ \frac{2}{\log_4 2000^6} + \frac{3}{\log_5 2000^6} $$
can be written as $\frac m n$​ where $m$ and $n$ are relatively prime positive integers.  Find $m+n$. -/
theorem algebra_97347 (m n : ℕ) (m_pos : 0 < m) (n_pos : 0 < n) (coprime : m.Coprime n)
      (eq : (2 / logb 4 (2000 ^ 6) + 3 / logb 5 (2000 ^ 6)) = (m : ℝ) / n) : m + n = 7 := by
  -- Our answer is $1+6 = 7$,
  suffices mneq : (m : ℤ) = 1 ∧ (n : ℤ) = 6 by
    rw_mod_cast[mneq.1, mneq.2]
  apply Rat.div_int_inj (a := m) (c := 1)
    (by assumption_mod_cast) (by norm_num) (by assumption_mod_cast) (by simp)
  rify
  rw[← eq]
  convert_to 2 * (logb 4 (2000 ^ 6))⁻¹ + 3 * (logb 5 (2000 ^ 6))⁻¹ = 1 / 6
  -- because $\frac{1}{\log_a b} = \log_b a$, we have
  -- $\frac{2}{\log_4 2000^6} + \frac{3}{\log_5 2000^6} = 2 \log_{2000^6} 4 + 3 \log_{2000^6} 5$
  rw[Real.inv_logb, Real.inv_logb,
  -- $=\log_{2000^6} 4^2 + \log_{2000^6} 5^3$
     ← Real.logb_rpow_eq_mul_logb_of_pos (by norm_num),
    ← Real.logb_rpow_eq_mul_logb_of_pos (by norm_num),
  -- $=\log_{2000^6} 4^2 \cdot 5^3$
    ← Real.logb_mul (by norm_num) (by norm_num)]
  -- $=\log_{2000^6} 2000$
  convert_to logb (2000^6) 2000 = ((6 : ℕ) : ℝ) ⁻¹
  · norm_num
  · simp
  -- $=1/6.$
  · rw[logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)]
    rw[Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]