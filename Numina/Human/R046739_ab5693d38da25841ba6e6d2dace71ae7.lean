import Mathlib

/-A very large number $x$ is equal to $2^23^34^45^56^67^78^89^9$. What is the smallest positive integer that, when multiplied with $x$, produces a product that is a perfect square?-/
theorem number_theory_14076 {x : ℕ} (hx : x = 2^2 * 3^3 * 4^4 * 5^5 * 6^6 * 7^7 * 8^8 * 9^9) :
    IsLeast {n | 0 < n ∧ ∃ k, k^2 = n * x} 105 := by
  obtain ⟨S, hS⟩ := (by simp  : ∃S, S = {n | 0 < n ∧ ∃ k, k^2 = n * x})
  rw [hS.symm]
  unfold IsLeast
  -- To get even exponents in the product, we need at least one more $3$, at least one more $5$, and at least one more $7$. That would bring us up to $3^45^67^8$, and everything would be good. And indeed, $3\cdot5\cdot7=\boxed{105}$
  -- so, we prove 105 in the S firstly.
  have _105_in_S : 105 ∈ S := by
    rw [hS]
    simp
    use 2 * 3^2 * 4^2 * 5^3 * 6^3 * 7^4 * 8^4 * 3^9
    rw [hx]
    simp
  use _105_in_S
  refine (le_csInf_iff' ?intro.right.hs).mp ?intro.right.a
  exact Set.nonempty_of_mem _105_in_S
  apply le_csInf (Set.nonempty_of_mem _105_in_S)
  rw [hS]
  simp
  -- than, we prove for any n in S, 105 is the least element.
  intro b hb k hk
  rw [hx] at hk
  -- For the product to be a perfect square, all the exponents need to be even, So we don't need to worry about factors that already have even exponents. We also don't need to worry about $9^9$ because $9$ is already a perfect square. The remaining factors are $3^3 5^5 7^7$.
  have : ∃ m, m * 2 * 3^1 * 4^2 * 5^2 * 6^3 * 7^3 * 8^4 * 3^9 = k := by
    have : 2 * 3^1 * 4^2 * 5^2 * 6^3 * 7^3 * 8^4 * 3^9 ∣ k := by
      apply (Nat.pow_dvd_pow_iff (by norm_num: 2 ≠ 0)).mp
      rw [hk]
      apply dvd_mul_of_dvd_right
      norm_num
    rcases this with ⟨m, hm⟩
    use m
    rw [mul_comm] at hm
    repeat rw [←mul_assoc] at hm
    exact hm.symm
  rcases this with ⟨m, hm⟩

  -- so, we get m^2 = b * 3 * 5 * 7
  have hm : m^2  = b * 3 * 5 * 7 := by
    rw [hm.symm] at hk
    linarith
  have dvd3 : 3 ∣ m := by
    have : 3 ∣ m^2 := by
      rw [hm, mul_comm b]
      repeat apply dvd_mul_of_dvd_left
      rfl
    rw [pow_two] at this
    have := (Prime.dvd_mul (Nat.Prime.prime (by norm_num))).mp this
    simp at this
    exact this
  have dvd5 : 5 ∣ m := by
    have : 5 ∣ m^2 := by
      rw [hm, mul_comm b, mul_comm (3 * b * 5), ←mul_assoc]
      apply dvd_mul_of_dvd_right
      rfl
    rw [pow_two] at this
    have := (Prime.dvd_mul (Nat.Prime.prime (by norm_num))).mp this
    simp at this
    exact this
  have dvd7 : 7 ∣ m := by
    have : 7 ∣ m^2 := by
      rw [hm, mul_comm b]
      apply dvd_mul_of_dvd_right
      rfl
    rw [pow_two] at this
    have := (Prime.dvd_mul (Nat.Prime.prime (by norm_num))).mp this
    simp at this
    exact this
  have : 3 * 5 * 7 ∣ m := by
    have : 3 * 5 * 7 = lcm (lcm 3 5) 7 := by decide
    rw [this]
    apply lcm_dvd
    apply lcm_dvd
    exact dvd3
    exact dvd5
    exact dvd7
  rcases this with ⟨n, hn⟩
  rw [hn] at hm
  by_cases h: n = 0
  . -- m = 0, which is not possible because 0 < b
    rw [h] at hm
    linarith
  have hn: n^2 * 105 = b := by
    rw [mul_pow, mul_comm, pow_two (3 * 5 * 7), ←mul_assoc] at hm
    rw [←mul_assoc, ←mul_assoc, ←mul_assoc] at hm
    simp at hm
    rw [mul_assoc, (by norm_num : 15 * 7 = 105)] at hm
    exact hm
  omega
