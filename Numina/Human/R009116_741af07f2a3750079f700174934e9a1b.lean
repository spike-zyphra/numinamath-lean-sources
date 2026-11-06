import Mathlib


/- Find the last three digits of the number $2003^{2002^{2001}}$. -/
theorem number_theory_604894 : (2003 ^ (2002 ^ 2001)) % 1000 = 241 := by
  -- result will be the same as the remainder when $3^{2002^{2001}}$ is divided by 1000, since $2003 \\equiv 3(\\bmod 1000)$.
  have (k : ℕ) : (2003 ^ k) % 1000 = 3 ^ k % 1000 := by rw [Nat.pow_mod]
  rewrite [this]
  -- we can evaluate $3^{2m}$ using the binomial theorem
  have binomial (m : ℕ) (hm : m ≥ 3) : 3 ^ (2 * m) % 1000 = (∑ i in Finset.range 3, (10 : ℤ) ^ i * (-1) ^ (m - i) * Nat.choose m i % 1000) % 1000 := by
    have (i : ℕ) (_ : i ∈ Finset.range (m + 1)) : (10 : ℤ) ^ i * (-1) ^ (m - i) * Nat.choose m i % 1000 = if i ≥ 3 then 0 else (10 : ℤ) ^ i * (-1) ^ (m - i) * Nat.choose m i % 1000 := by
      by_cases h : i ≥ 3
      · simp [h]
        suffices h' : 10 ^ 3 ∣ (10 : ℤ) ^ i
        · rw [mul_assoc]
          exact Dvd.dvd.mul_right h' ((-1) ^ (m - i) * ↑(m.choose i))
        · exact pow_dvd_pow 10 h
      · simp [h]
    rw [pow_mul, show (3 : ℤ) ^ 2 = 9 by norm_num, show 9 = 10 + (-1) by norm_num]
    rw [add_pow 10 (-1) m, Finset.sum_int_mod, Finset.sum_congr rfl this, Finset.sum_ite]
    simp
    congr
    ext x
    simp
    intro h
    linarith
  have cast (k a : ℕ) (h : (3 : ℤ) ^ k % 1000 = a) : (3 ^ k : ℕ) % (1000 : ℕ) = a := by
    have : ((3 ^ k : ℕ) % (1000 : ℕ) : ℕ) = (3 : ℤ) ^ k % 1000 := by norm_cast
    rw [←this] at h
    norm_cast at h
  -- Using this, we can check that $3^{100} \equiv 1(\bmod 1000)$
  have h100 : 3 ^ 100 % 1000 = 1 := by
    apply cast 100 1
    rw [show 100 = 2 * 50 by norm_num]
    have h := binomial 50 (by norm_num)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, Nat.choose_two_right] at h
    rw [h]
    simp
  -- 3 ^ k % 1000 = 3 ^ (k % 100) % 1000
  have hmod100 (k : ℕ) : 3 ^ k % 1000 = 3 ^ (k % 100) % 1000 := by
    suffices h : 3 ^ k ≡ 3 ^ (k % 100) [MOD 1000] by exact h
    have h : 3 ^ 100 ≡ 1 [MOD 1000] := by
      have (a b : ℕ) (h : a % 1000 = b) : b ≡ a [MOD 1000] := by
        refine Nat.modEq_of_dvd ?_; refine Int.dvd_sub_of_emod_eq ?h; norm_cast
      have h := this (3 ^ 100) 1 h100
      exact h
    have h' (t : ℕ) : 3 ^ (100 * t) ≡ 1 [MOD 1000] := by
      have : 3 ^ (100 * t) = (3 ^ 100) ^ t := by rw [Nat.pow_mul]
      rw [this]
      have : 1 = 1 ^ t := by rw [Nat.one_pow]
      rw [this]
      apply Nat.ModEq.pow
      exact h
    have : 3 ^ k = 3 ^ (k % 100 + 100 * (k / 100)) := by
      rw [Nat.mod_add_div k 100]
    rw [this]
    rw [Nat.pow_add]
    have h'' := h' (k / 100)
    have : 3 ^ (k % 100) = 3 ^ (k % 100) * 1 := by rw [Nat.mul_one]
    nth_rw 2 [this]
    apply Nat.ModEq.mul
    exact rfl
    exact h''
  rw [hmod100]
  -- now we wish to find the remainder when $2002^{2001}$ is divided by 100.
  have hpower : 2002 ^ 2001 % 100 = 52 := by
    rw [Nat.pow_mod 2002 2001 100]
    have : 2002 % 100 = 2 := by norm_num
    rw [this]
    have lem_2_10 : 2 ^ 10 ≡ -1 [ZMOD 25] := rfl
    have lem_2_1999 : (2 ^ 1999 : ℤ) ≡ 13 [ZMOD 25] := by
      calc
        2 ^ 1999 ≡ 2 ^ (10 * 199) * 2 ^ 9 [ZMOD 25] := by
          rw [(by rfl : 1999 = 10 * 199 + 9), pow_add]
        _ ≡ (2 ^ 10) ^ 199 * 2 ^ 9 [ZMOD 25] := by rw [pow_mul]
        _ ≡ (-1) ^ 199 * 2 ^ 9 [ZMOD 25] := by
          suffices h : (2 ^ 10) ^ 199 ≡ (-1) ^ 199 [ZMOD 25] by apply Int.ModEq.mul_right (2 ^ 9) h
          apply Int.ModEq.pow
          exact lem_2_10
        _ ≡ (-1) * 2 ^ 9 [ZMOD 25] := by
          suffices h : (-1) ^ 199 = -1 by rw [h]
          apply pow_eq_neg_one_iff.mpr
          norm_num
          exact Nat.odd_iff.mpr rfl
        _ ≡ 13 [ZMOD 25] := by rfl
    have lem_2_1999' : 2 ^ 1999 ≡ 13 [MOD 25] := by
      apply Nat.modEq_iff_dvd.mpr
      rw [Nat.cast_pow]
      exact Int.modEq_iff_dvd.mp lem_2_1999
    have : 2001 = 1999 + 2 := by norm_num
    simp only [this, pow_add]
    rw [(by rfl : 52 = 13 * 4 % 100), (by rfl : 2 ^ 2 = 4)]
    suffices h : 2 ^ 1999 * 4 ≡ 13 * 4 [MOD 100] by rw [h]
    rw [(by rfl : 100 = 25 * 4)]
    apply (Nat.ModEq.mul_right_cancel_iff' (by simp : 4 ≠ 0)).mpr
    exact lem_2_1999'
  rw [hpower]
  -- so $$ 2003^{2002^{2001}} \equiv 3^{52}(\bmod 1000) \equiv 1-20 \cdot 13+1300 \cdot 25 \equiv 241(\bmod 1000) $$
  -- using equation (1). So the last 3 digits of $2003^{2002^{2001}}$ are 241.
  have : 3 ^ 52 % 1000 = 241 := by
    apply cast 52 241
    rw [show 52 = 2 * 26 by norm_num]
    have h := binomial 26 (by norm_num)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, Nat.choose_two_right] at h
    rw [h]
    simp
  exact this
