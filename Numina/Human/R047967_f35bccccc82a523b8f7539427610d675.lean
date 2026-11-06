import Mathlib

/- Find all positive integers $x, y, z$ such that

$$
45^{x}-6^{y}=2019^{z}
$$ -/
theorem number_theory_606175 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : 45 ^ x - 6 ^ y = 2019 ^ z) :
    (x, y, z) = (2, 1, 1) := by
  -- A lemma for determining 6 ^ y ≤ 45 ^ x.
  have h' : 45 ^ x - 6 ^ y > 0 := by
    calc
      45 ^ x - 6 ^ y = 2019 ^ z := h
      _ > 0 := by positivity
  -- Transform the equation into modulo 5 form to analyze the parity of z.
  have h1 := congr_arg (· % 5) h
  simp at h1
  -- Transform the equation into modulo 4 form to analyze the value of y.
  have h2 := congr_arg (· % 4) h
  simp at h2
  -- Transform the equation into modulo 9 form to analyze the value of z.
  have h3 := congr_arg (· % 9) h
  simp at h3
  -- Based on the modulo 5 analysis, determine that z is odd.
  have h4 : z % 2 = 1 := by
    -- Use the modulo 5 result and number theory to determine the parity of z.
    rw [Nat.pow_mod] at h1
    norm_num at h1
    -- Convert h1 into equation of integers.
    zify at h1
    rw [<-Int.subNatNat_of_le (by omega), Int.subNatNat_eq_coe, Int.sub_emod] at h1
    simp at h1
    rw [show (45 ^ x % 5 : ℤ) = (45 ^ x % 5 : ℕ) by norm_cast, show (6 ^ y % 5 : ℤ) = (6 ^ y % 5 : ℕ) by norm_cast] at h1
    nth_rewrite 1 [Nat.pow_mod] at h1
    nth_rewrite 2 [Nat.pow_mod] at h1
    simp at h1
    rw [zero_pow (by omega)] at h1
    simp at h1
    -- Proof by contradiction that z is Odd.
    have : Odd z := by
      contrapose h1
      simp [Even] at h1
      obtain ⟨r, h1⟩ := h1
      rw [h1, <-mul_two, mul_comm, pow_mul]
      norm_cast
      simp [Nat.pow_mod]
    simp [Odd] at this
    omega
  -- Based on the modulo 4 analysis, determine that y is 1.
  have h5 : y = 1 := by
    -- Use the modulo 4 result and number theory to determine the value of y.
    rw [Nat.pow_mod] at h2
    norm_num at h2
    -- Convert h2 into equation of integers.
    zify at h2
    rw [<-Int.subNatNat_of_le (by omega), Int.subNatNat_eq_coe, Int.sub_emod] at h2
    simp at h2
    rw [show (45 ^ x % 4 : ℤ) = (45 ^ x % 4 : ℕ) by norm_cast, show (6 ^ y % 4 : ℤ) = (6 ^ y % 4 : ℕ) by norm_cast] at h2
    nth_rewrite 1 [Nat.pow_mod] at h2
    nth_rewrite 2 [Nat.pow_mod] at h2
    simp at h2
    -- Prove that contradiction that y < 2 (using the fact just proved that z % 2 = 1).
    have : y < 2 := by
      contrapose! h2
      apply Nat.le.dest at h2
      obtain ⟨k, h2⟩ := h2
      rw [show (2 ^ y % 4 : ℤ) = (2 ^ y % 4 : ℕ) by norm_cast, <-h2, pow_add, Nat.mul_mod]
      simp
      have h5 := Nat.mod_add_div z 2
      rw [show (3 ^ z % 4 : ℤ) = (3 ^ z % 4 : ℕ) by norm_cast, <-h5, h4, pow_add, pow_mul, Nat.mul_mod]
      nth_rewrite 2 [Nat.pow_mod]
      simp
    -- Conclude that y is 1.
    omega
  -- Based on the modulo 9 analysis, determine that z is 1.
  have h6 : z = 1 := by
    -- Use the modulo 9 result and number theory to determine the value of z.
    rw [Nat.pow_mod] at h3
    norm_num at h3
    -- Convert h3 into equation of integers.
    zify at h3
    rw [<-Int.subNatNat_of_le (by omega), Int.subNatNat_eq_coe, Int.sub_emod] at h3
    simp at h3
    -- Substitute y = 1 into h3 and simplify.
    rw [h5, show (45 ^ x % 9 : ℤ) = (45 ^ x % 9 : ℕ) by norm_cast, Nat.pow_mod] at h3
    simp [zero_pow (hx.ne')] at h3
    -- Prove that contradiction that z > 1.
    have : z ≤ 1 := by
      contrapose! h3
      apply Nat.le.dest at h3
      obtain ⟨k, h3⟩ := h3
      simp [<-h3, pow_add]
    -- Conclude that z is 1.
    omega
  -- Substitute y = 1 and z = 1 to solve for x = 2.
  have h7 : x = 2 := by
    -- Use the known values of y and z to solve for x.
    rw [h5, h6] at h
    replace h : 45 ^ x = 45 ^ 2 := by omega
    exact Nat.pow_right_injective (by norm_num : 1 < 45) h
  simp
  trivial
