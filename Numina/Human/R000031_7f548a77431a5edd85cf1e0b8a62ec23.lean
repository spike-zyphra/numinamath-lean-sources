import Mathlib

/-- Auxiliary lemma : if $n <0$ and $n+k<0$ where $n$ and $k$ are integers, then
  $\left | n + k \right | = \left | n \right | - k $. -/
lemma Int.natAbs_add' {n k : ℤ} (hn : n < 0) (h : n + k < 0) :
  (n + k).natAbs = n.natAbs - k:= by
    rw [Int.ofNat_natAbs_of_nonpos (le_of_lt h), Int.ofNat_natAbs_of_nonpos (le_of_lt hn)]
    ring

/-- Auxiliary lemma : if $n <0$, $0<k$ and $n+ k < 0$, then we have $\left | k \right | < \left | n \right |$. -/
lemma aux2' {n k : ℤ} (hn : n < 0) (hk : 0 < k) (h : n + k < 0) :
  k.natAbs < n.natAbs := by
    rw [add_comm, Int.add_lt_iff, add_zero] at h
    rw [Int.natAbs_lt_iff_sq_lt, sq_lt_sq, abs_eq_self.2 (le_of_lt hk), abs_eq_neg_self.2 (le_of_lt hn)]
    assumption

/-- Auxiliary lemma :  2 divides the product of 2 consecutive natural numbers. -/
lemma prod_cons2_dvd2 (n : ℕ) : 2 ∣ n * (n + 1) := by
  by_cases h : n % 2 = 0
  · replace h :=  Nat.dvd_of_mod_eq_zero h
    exact Dvd.dvd.mul_right h (n + 1)
  · have : n % 2 < 2 := Nat.mod_lt n (by linarith)
    have h : n % 2 = 1 := by simp at *; linarith
    have : (n + 1) % 2 = 0 := by rw [Nat.add_mod]; simp [h]
    have := Nat.dvd_of_mod_eq_zero this
    exact Dvd.dvd.mul_left this n

/-- Auxiliary lemma :  6 divides by the product of three consecutive natural numbers. -/
lemma prod_cons3_dvd6 (n : ℕ) : 6 ∣ n * (n + 1) * (n + 2) := by
  have h1 : 2 ∣ n * (n + 1) * (n + 2) := by
    have := prod_cons2_dvd2 n
    exact Dvd.dvd.mul_right this (n + 2)
  have h2 : 3 ∣ n * (n + 1) * (n + 2) := by
    have h3 : n % 3 < 3 := Nat.mod_lt n (by linarith)
    set m := (n % 3) with hm
    interval_cases m
    · have := Nat.dvd_of_mod_eq_zero hm.symm
      rw [mul_assoc]; exact Dvd.dvd.mul_right this ((n + 1) * (n + 2))
    · have hm : (n + 2) % 3 = 0 := by rw [Nat.add_mod]; rw [←hm]
      have := Nat.dvd_of_mod_eq_zero hm
      exact Dvd.dvd.mul_left this (n * (n + 1))
    · have hm : (n + 1) % 3 = 0 := by rw [Nat.add_mod,←hm]
      have := Nat.dvd_of_mod_eq_zero hm
      nth_rw 2 [mul_comm]; rw [mul_assoc]
      exact Dvd.dvd.mul_right this (n * (n + 2))
  exact Nat.Prime.dvd_mul_of_dvd_ne (by norm_num) Nat.prime_two Nat.prime_three h1 h2

/-- Auxiliary lemma : 6 divides by the product of three consecutive integers. -/
lemma prod_cons3_dvd6' (n : ℤ) : ((6 :ℕ) : ℤ) ∣ n * (n + 1) * (n + 2) := by
  --convert prod_cons3_dvd6
  by_cases h : n * (n + 1) * (n + 2) = 0
  · rw [h]; simp
  · simp at h; push_neg at h
    rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_mul]
    by_cases h1 : 0 < n
    · convert prod_cons3_dvd6 n.natAbs
      · rw [Int.natAbs_add_of_nonneg (by linarith) (by simp), Int.natAbs_one]
      · rw [Int.natAbs_add_of_nonneg (by linarith) (by simp)]; simp
    · simp at h1
      have h1 : n < 0 := lt_of_le_of_ne h1 h.1.1
      have h2 : n + 1 < 0 := lt_of_le_of_ne (Int.add_one_le_of_lt h1) h.1.2
      have h3 : n + 2 < 0 := lt_of_le_of_ne (by
        have := Int.add_one_le_of_lt h2; rw [add_assoc] at this; simp at this; exact this) h.2
      convert prod_cons3_dvd6 (n + 2).natAbs using 1
      have : (2 : ℤ).natAbs < n.natAbs := aux2' h1 (by simp) h3
      have h4 : (n + 2).natAbs + (1 : ℤ) = (n + 1).natAbs := by
        rw [Int.natAbs_add' h1 h3, Int.natAbs_add' h1 h2]; linarith
      have h5 : (n + 2).natAbs + (2 : ℤ) = n.natAbs := by
        rw [Int.natAbs_add' h1 h3]; linarith
      have : (n.natAbs : ℤ) * (n + 1).natAbs * (n + 2).natAbs =
      (n + 2).natAbs * ((n + 2).natAbs + 1) * ((n + 2).natAbs + 2) := by
        rw [h4, h5]; ring
      convert this using 2
      norm_cast

/-- Auxiliary lemma : $5 \mid n^5 - n. $-/
lemma dvd5 (n : ℤ) : 5 ∣ n ^ 5 - n := by
  apply Int.ModEq.dvd
  have h2 : n % 5 < 5 := by refine Int.emod_lt_of_pos n (by simp)
  have h3 : 0 ≤ n % 5 := by refine Int.emod_nonneg n (by simp)
  set m := n % 5 with hm
  interval_cases m
  · have hm : 0 ≡ n [ZMOD 5] := hm
    exact hm.symm.trans (Int.ModEq.pow 5 hm)
  · have hm : 1 ≡ n [ZMOD 5] := hm
    exact hm.symm.trans (Int.ModEq.pow 5 hm)
  · have hm : 2 ≡ n [ZMOD 5] := hm
    exact hm.symm.trans (Int.ModEq.pow 5 hm)
  · have hm : 3 ≡ n [ZMOD 5] := hm
    exact hm.symm.trans (Int.ModEq.pow 5 hm)
  · have hm : 4 ≡ n [ZMOD 5] := hm
    exact hm.symm.trans (Int.ModEq.pow 5 hm)

/-- Let $\( n \)$ be an integer. Determine the remainder $\( b \)$ of $\( n^{a} - n \)$ divided by 30.-/
theorem number_theory_4059 (n : ℤ) : 30 ∣ (n ^ 5 - n)  := by
  -- Observe that for any integer $n$, $n^5 - n = n(n^4-1) = n(n^2+1)(n^2-1)$
  have h1 : n ^ 5 - n = (n - 1) * n * (n + 1) * (n ^ 2 + 1) := by
    have sq1 : (1 : ℤ) = 1 ^ 2 := by norm_num
    have sq4 : n ^ 4 = (n ^ 2) ^ 2 := by rw [←pow_mul]
    calc
      _ = n * (n ^ 4 - 1) := by ring
      _ = n * (n ^ 2 - 1) * (n ^ 2 + 1) := by
        nth_rw 1 [sq1, sq4, sq_sub_sq]; ring
      _ = _ := by rw [sq1,sq_sub_sq]; ring
  -- $6 \mid n^5 - n$.
  have dvd6 : 6 ∣ n ^ 5 - n  := by
    rw [h1]
    convert dvd_mul_of_dvd_left (prod_cons3_dvd6' (n - 1)) (n ^ 2 + 1)  using 1
    ring
  -- Because 5 and 6 are coprime, we get $5 * 6 \mid n^5 - n$.
  exact IsCoprime.mul_dvd (by norm_num) dvd6 (dvd5 n)
