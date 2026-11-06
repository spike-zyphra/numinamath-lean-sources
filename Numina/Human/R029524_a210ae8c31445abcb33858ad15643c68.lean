import Mathlib

/- Let $a, b, c, d$ be positive integers such that $\log_a b = \frac{3}{2}$ and $\log_c d = \frac{5}{4}$. If $a - c = 9$,
 find the value of $b - d$. -/
theorem algebra_8568 {a b c d : ℕ} (ha : 1 < a) (hb : 0 < b) (hc : 1 < c) (hd : 0 < d)
    (h1 : Real.logb a b = (3 : ℝ) / 2) (h2 : Real.logb c d = 5 / 4) (h3 : a - c = 9) : b - d = 93 := by
  -- we simplify the logarithm equations firstly
  rw [Real.logb_eq_iff_rpow_eq] at h1 h2
  replace h1: a ^ 3 = b ^ 2 := by -- first equation
    replace h1: ((a: ℝ) ^ ((3: ℝ) / 2)) ^ 2 = ↑b ^ 2 := by
      simp [h1]
    have eq: ((a: ℝ) ^ ((3: ℝ) / 2)) ^ 2 = ↑a ^ 3 := by
      have o: 0 ≤ (a: ℝ) := by
        simp
      have j:= Real.rpow_mul o ((3: ℝ) / 2) 2
      rw [show ((a: ℝ) ^ ((3: ℝ) / 2)) ^ (2: ℝ) = (↑a ^ ((3: ℝ) / 2)) ^ (2: ℕ) by simp] at j
      rw [← j]
      rw [show (3: ℝ) / 2 * 2 = 3 by norm_num]
      norm_cast
    rw [eq] at h1
    norm_cast at h1
  replace h2: c ^ 5 = d ^ 4 := by  -- second equation
    replace h2: ((c: ℝ) ^ ((5: ℝ) / 4)) ^ 4 = ↑d ^ 4 := by
      simp [h2]
    have eq: ((c: ℝ) ^ ((5: ℝ) / 4)) ^ 4 = ↑c ^ 5 := by
      have o: 0 ≤ (c: ℝ) := by
        simp
      have j:= Real.rpow_mul o (5 / 4) 4
      rw [show ((c: ℝ) ^ ((5: ℝ) / 4)) ^ (4: ℝ) = (↑c ^ ((5: ℝ) / 4)) ^ (4: ℕ) by norm_cast] at j
      rw [← j]
      rw [show ((5: ℝ) / 4) * 4 = 5 by norm_num]
      norm_cast
    rw [eq] at h2
    norm_cast at h2
  -- then we show a = k ^ 2, b = k ^ 3
  have da: a ∣ b := by
    have o: a ^ 2 ∣ b ^ 2 := by
      rw [← h1]
      apply Nat.pow_dvd_pow
      norm_num
    rw [Nat.pow_dvd_pow_iff] at o
    exact o
    norm_num
  apply exists_eq_mul_right_of_dvd at da
  obtain ⟨k,hk⟩ := da
  simp [hk] at h1
  have ak: a = k ^ 2 := by
    nlinarith
  simp [ak] at hk
  have bk: b = k ^ 3 := by
    nlinarith
  clear h1 hk
-- then we show c = l ^ 4, d = l ^ 5
  have dc: c ∣ d := by
    have o: c ^ 4 ∣ d ^ 4 := by
      rw [← h2]
      apply Nat.pow_dvd_pow
      norm_num
    rw [Nat.pow_dvd_pow_iff] at o
    exact o
    norm_num
  apply exists_eq_mul_right_of_dvd at dc
  obtain ⟨l,hl⟩ := dc
  have pl: 0 < l := by nlinarith
  simp [hl] at h2
  have lc: c = l ^ 4 := by
    rw [show (c * l) ^ 4 = c ^ 4 * l ^ 4 by ring] at h2
    zify
    zify at h2
    replace h2: (c: ℤ) ^ 5 - ↑c ^ 4 * ↑l ^ 4 = 0 := by omega
    rw [show (c: ℤ) ^ 5 - ↑c ^ 4 * ↑l ^ 4 = (c: ℤ) ^ 4 * (↑c - ↑l ^ 4) by ring] at h2
    simp at h2
    have o: ¬ c = 0 := by omega
    simp [o] at h2
    linarith
  simp [lc] at hl
  have ld: d = l ^ 5 := by
    nlinarith
  clear h2 hl
  rw [lc,ak] at h3
  have o: l ^ 2 ≤ k := by
    by_contra! o
    have o1: k ^ 2 < l ^ 4 := by nlinarith
    omega
  -- then we factor left side of h3
  have eq: k ^ 2 - l ^ 4 = (k - l ^ 2) * (k + l ^ 2) := by
    zify
    have o1: ↑(k ^ 2 - l ^ 4) = (k: ℤ) ^ 2 - ↑l ^ 4 := by
      rw [Nat.cast_sub]
      norm_cast
      omega
    rw [o1]
    have o2: ↑(k - l ^ 2) = (k: ℤ) - ↑l ^ 2 := by
      rw [Nat.cast_sub]
      norm_cast
      omega
    rw [o2]
    ring
  rw [eq] at h3
  -- from h3, we can solve k and l
  have ineq: (k - l ^ 2) ^ 2 ≤ 9 := by
    have i: k - l ^ 2 ≤ k + l ^ 2 := by
      omega
    rw [← h3]
    nlinarith
  replace ineq: k - l ^ 2 ≤ 3 := by nlinarith
  replace o: 0 ≤ k - l ^ 2 := by linarith
  have s:  k - l ^ 2 = 0 ∨ k - l ^ 2 = 1 ∨ k - l ^ 2 = 2 ∨ k - l ^ 2 = 3 := by
    omega
  rcases s with s | s | s | s
  . simp [s] at h3
  . simp [s] at h3
    have sk: k = 5 := by omega
    have sl: l ^ 2 = 4 := by omega
    replace sl: l = 2 := by
      have o1: l ≤ 2 := by
        by_contra! o1
        replace o1: 3 ≤ l := by omega
        have j: 9 ≤ 4 := by
          rw [← sl]
          rw [show 9 = 3 ^ 2 by norm_num]
          apply Nat.pow_le_pow_left
          exact o1
        tauto
      have o2: 2 ≤ l := by
        by_contra! o2
        replace o2: l = 1 := by omega
        simp [o2] at sl
      omega
    simp [sk,sl] at *
    omega
  . simp [s] at h3
    have j: 2 ∣ 9 := by
      rw [← h3]
      simp
    omega
  . simp [s] at h3
    replace h3: k + l ^ 2 = 3 := by omega
    have sl: l ^ 2 = 0 := by omega
    simp at sl
    simp [sl] at pl

  -- tackle some small details
  . simp
    omega
  . simp
    omega
  . simp
    exact hd
  . simp
    omega
  . simp
    omega
  . simp
    omega