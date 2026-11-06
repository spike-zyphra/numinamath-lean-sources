import Mathlib

open Real

/-- Define binary operations ♢ and ♡ by
a ♢ b=a^(log⁡7(b)) and a ♡ b=a^(1/log⁡7(b))
for all real numbers a and b for which these expressions are defined.
The sequence a_n is defined recursively by a_3=3 ♡ 2 and
a_n=(n ♡ (n−1)) ♢ a_(n−1)
for all integers n≥4. To the nearest integer, what is log⁡7(a_2019)?
(A) 8(B) 9(C) 10(D) 11(E) 12 -/
theorem algebra_93000 {a : ℕ → ℝ}
    (ha3 : a 3 = 3 ^ (1 / logb 7 2))
    (han : ∀ n ≥ 4, a n = (n ^ (1 / logb 7 (n - 1))) ^ logb 7 (a (n - 1))) :
    round (logb 7 (a 2019)) = 11 := by
  -- By definition, the recursion becomes
  -- a_n = (n^(1/log7(n-1)))^log7(a_(n-1)) = n^(log7(a_(n-1))/log7(n-1)).
  have : ∀ n ≥ 4, a n = n ^ (logb 7 (a (n-1)) / logb 7 (n-1)) := by
    intro n hn
    rw[han n hn]
    rw[← rpow_mul (by linarith)]
    congr 1
    field_simp
  -- By the change of base formula, this reduces to
  -- a_n = n ^ log_(n-1) (a_(n-1)).
  have : ∀ n ≥ 4, a n = n ^ (logb (n-1) (a (n-1))) := by
    intro n hn
    rw[this n hn]
    congr 1
    have n0 : (n : ℝ) - 1 ≠ 0 := by
      intro h; rw[sub_eq_iff_eq_add] at h; rw_mod_cast[h] at hn; contradiction
    have n1 : (n : ℝ) - 1 ≠ 1 := by
      intro h; rw[sub_eq_iff_eq_add] at h; rw_mod_cast[h] at hn; contradiction
    have nm1 : (n : ℝ) - 1 ≠ -1 := by
      intro h; rw[sub_eq_iff_eq_add] at h; norm_num at h; rw[h] at hn; contradiction
    rw[div_eq_iff]
    · rw[mul_comm, Real.mul_logb n0 n1 nm1]
    · intro h
      simp only [logb_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, n0, n1, nm1, or_self,
        or_false, false_or] at h
      norm_num at h
  -- Thus we have log_n(a_n) = log_(n-1)(a_(n-1))
  have : ∀ n ≥ (4 : ℕ), logb n (a n) = logb (n-1) (a (n-1)) := by
    intro n hn
    rw[this n hn]
    rw[logb_rpow]
    · norm_cast
      linarith
    · norm_cast
      linarith
  -- and for all m >= 3, the value of log_m(a_m) must be some constant value k (by induction).
  have : ∀ n ≥ (4 : ℕ), logb n (a n) = logb 2 7 := by
    intro n hn
    induction n, hn using Nat.le_induction with
  -- We now compute k from a_3. It is given that a_3 = 3^(1/log7(2))
  -- so k = log_3(a_3) = log_3(3^(1/log7(2))) = log_2(7).
    | base =>
      specialize this 4 le_rfl
      rw[this]
      change logb (↑4 - 1) (a 3) = logb 2 7
      rw[ha3]
      simp only [one_div]
      norm_num
      rw[inv_logb]
    | succ n hmn ih =>
      rw[← ih]
      convert this (n+1) (le_trans hmn (Nat.le_succ _))
      simp
  -- Now, we must have log_2019(a_2019) = log_2(7). At this point, we can simply switch some bases around.
  have : logb 2019 (a 2019) = logb 2 7 := this 2019 (by simp)
  rw[← Real.log_div_log, ← Real.log_div_log] at this
  rw[← Real.log_div_log]
  -- From log (a_2019)/log 2019 = log 7 / log 2
  rw[div_eq_iff (by norm_num)] at this
  rw[this]
  -- we get log7(a_2019) = log2(2019). Rounded, this is 11:
  convert_to round (log 2019 / log 2) = 11 using 2
  · field_simp
    ring
  · rw[Real.log_div_log]
    rw[round_eq]
    rw[Int.floor_eq_iff]
    constructor
    · rw[← sub_le_iff_le_add]
      rw[Real.le_logb_iff_rpow_le]
      -- log2(2019) is larger than 10.5, since 2019 is larger than 1024 * sqrt 2.
      convert_to 2048 / sqrt 2 ≤ 2019
      · rw[rpow_sub]
        · rw[rpow_div_two_eq_sqrt]
          · norm_num
          · simp
        · simp
      · apply div_le_of_le_mul₀
        · simp
        · simp
        · have : 11 / 10 < √ 2 := by
            rw[lt_sqrt]
            · linarith
            · linarith
          trans 2019 * 11/10
          · norm_num
          · linarith
      · norm_num
      · norm_num
    -- But 2024 = 2^11, so it is smaller than 11, hence the rounded number must be 11.
    · have : logb 2 2019 < 11 := by rw[logb_lt_iff_lt_rpow] <;> norm_num
      trans 11 + 1/2
      · linarith
      · linarith