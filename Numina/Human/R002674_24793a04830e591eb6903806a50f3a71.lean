import Mathlib
/-- An infinite geometric series has sum 2005.
   A new series, obtained by squaring each term of the original series,
   has 10 times the sum of the original series. The common ratio of the
   original series is m/n​ where m and n are relatively prime integers. Find m+n. -/
theorem algebra_98616 {a r : ℝ} (ha : a ≠ 0) (hr2 : |r| < 1) (h : ∑' n : ℕ, a * r ^ n = 2005) {m n : ℕ} (hmn : m.Coprime n)
    (hm : 0 < m) (hn : 0 < n)
    (h' : ∑' n : ℕ, (a * r ^ n) ^ 2 = 10 * 2005)
    (eq : r = m / n) : m + n = 802 := by
  -- the answer is 399 + 403 = 802
  suffices mneq : (m : ℤ) = 399 ∧ (n : ℤ) = 403 by
    rw_mod_cast[mneq.1, mneq.2]
  -- Let's call the first term of the geometric series a and the common ratio r, so
  -- 2005 = a + ar + ar^2 + ⋯.
  -- Using the sum formula for geometric series and the assumption, we have a/(1-r) = 2005.
  have geom1 : a / (1 - r) = 2005 := by
    rw[tsum_mul_left, tsum_geometric_of_abs_lt_one hr2] at h
    rw[← h]
    ring
  -- Then we form a new series, a^2 + a^2 r^2 + a^2 r^4 + ⋯
  -- We know this series has sum 20050 = a^2 / (1 - r^2).
  have geom2 : a^2 / (1 - r^2) = 10 * 2005 := by
    conv at h' => lhs; rhs; intro n; rw[mul_pow, pow_right_comm]
    rw[tsum_mul_left, tsum_geometric_of_abs_lt_one ?rightabs] at h'
    case rightabs => rw[abs_pow, sq_lt_one_iff₀ (by simp)]; assumption
    rw[← h']
    ring
  have not_one : 1 - r ≠ 0 := by
    intro h
    have : r = 1 := by linarith
    rw[this] at hr2
    simp at hr2
  have not_neg_one : 1 + r ≠ 0 := by
    intro h
    have : r = -1 := by linarith
    rw[this] at hr2
    simp at hr2
  -- Dividing this equation by a/(1-r), we get 10 = a/(1+r)
  have : a / (1 + r) = 10 := by
    convert_to (a ^ 2 / (1 - r^2))/(a/(1-r)) = 10
    · have : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
      rw[this]
      rw[div_div_div_eq]
      rw[mul_assoc, mul_div_assoc]
      rw[div_mul_cancel_left₀ not_one, mul_inv, pow_two, mul_assoc, mul_left_comm (c := a⁻¹),
         mul_inv_cancel₀ ha]
      ring
    · rw[geom2, geom1]
      norm_num
  apply Rat.div_int_inj (a := m) (c := _) (by assumption_mod_cast) (by norm_num) (by assumption_mod_cast) (by norm_num)
  rify
  rw[← eq]
  -- Then a = 2005 - 2005r
  have a1 : a = 2005 * (1 - r) := by rwa[← div_eq_iff not_one]
  -- and a = 10 + 10r
  have a2 : a = 10 * (1 + r) := by rwa[← div_eq_iff not_neg_one]
  -- so 2005 - 2005 r = 10 + 10 r
  have : 2005 - 2005 * r = 10 + 10 * r := by linarith
  -- 1995 = 2015r
  have : 1995 = 2015 * r := by linarith
  -- and finally r = 1995/2015
  have : r = 1995 / 2015 := by linarith
  -- = 399 + 403
  rw[this]
  norm_num