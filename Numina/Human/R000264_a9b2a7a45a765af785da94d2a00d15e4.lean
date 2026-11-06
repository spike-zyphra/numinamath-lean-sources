import Mathlib

/- Prove that the number  $\lfloor (2+\sqrt5)^{2019} \rfloor$  is not prime.-/
theorem number_theory_8747 : ¬ Prime ⌊(2 + √5) ^ 2019⌋ := by
  have sq_two_add_sqrt : (2 + √5) ^ 2 = 9 + 4 * √5 := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring
  have sq_two_sub_sqrt : (2 - √5) ^ 2 = 9 - 4 * √5 := by
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring
  have floor_int_add_small (n : ℤ) {δ : ℝ} (hδ : 0 < δ ∧ δ < 1) : ⌊n + δ⌋ = n := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  -- We can define  $a_n$  by  $a_n=4a_{n-1}+a_{n-2}, a_0=2, a_1=4$ .
  -- By induction, we know   $$ a_n={(2+\sqrt{5})^n+(2-\sqrt{5})^n} $$
  set a : ℕ → ℝ := fun n => (2 + √5) ^ n + (2 - √5) ^ n with ha
  have ha0 : a 0 = 2 := by norm_num [ha]
  have ha1 : a 1 = 4 := by norm_num [ha]
  have han (n : ℕ) : a (n + 2) = 4 * a (n + 1) + a n := by
    simp [ha]
    repeat rw [pow_add]
    rw [sq_two_add_sqrt, sq_two_sub_sqrt, pow_one, pow_one]
    ring
  -- It's obvious that 2 < an for 0 < n.
  have two_lt_an {n : ℕ} (hn : 0 < n) : 2 < a n := by
    induction' n using Nat.strongRecOn with n ih
    rcases lt_or_le n 3
    . interval_cases n
      . norm_num [ha1]
      . norm_num [han, ha0, ha1]
    rw [show n = n - 2 + 2 by omega, han]
    have := ih (n - 2 + 1) (by omega) (by omega)
    have := ih (n - 2) (by omega) (by omega)
    linarith
  -- It's obvious that an is actually natural numbers.
  have han_eq_natCast (n : ℕ) : ∃ m : ℕ, m = a n := by
    induction' n using Nat.strongRecOn with n ih
    rcases lt_or_le n 2
    . interval_cases n
      . use 2; norm_num [ha0]
      . use 4; norm_num [ha1]
    rw [show n = n - 2 + 2 by omega, han]
    obtain ⟨x, hx⟩ := ih (n - 2 + 1) (by omega)
    obtain ⟨y, hy⟩ := ih (n - 2) (by omega)
    use 4 * x + y
    rw [← hx, ← hy]
    norm_cast
  have han_floor_eq_self (n : ℕ) : ⌊a n⌋ = a n := by
    obtain ⟨m, hm⟩ := han_eq_natCast n
    rw [← hm]
    simp
  -- It's obvious that an are even.
  have two_dvd_an_floor (n : ℕ) : 2 ∣ ⌊a n⌋ := by
    induction' n using Nat.strongRecOn with n ih
    rcases lt_or_le n 2
    . interval_cases n
      . norm_num [ha0]
      . norm_num [ha1]
    rw [show n = n - 2 + 2 by omega, han]
    obtain ⟨x, hx⟩ := ih (n - 2 + 1) (by omega)
    obtain ⟨y, hy⟩ := ih (n - 2) (by omega)
    use 4 * x + y
    rify at hx hy ⊢
    rw [← han]
    rw [han_floor_eq_self] at hx hy ⊢
    rw [han, hx, hy]
    ring
  obtain ⟨x, hx⟩ := han_eq_natCast 2019
  have two_lt_x : 2 < x := by
    rify
    rw [hx]
    apply two_lt_an
    norm_num
  have two_dvd_x : 2 ∣ x := by
    zify
    obtain ⟨k, hk⟩ := two_dvd_an_floor 2019
    use k
    rw [← hk]
    rify
    rw [hx, han_floor_eq_self]
  simp [ha] at hx
  -- 0 < -(2 - √5) ^ 2019 ∧ -(2 - √5) ^ 2019 < 1
  have : 0 < -(2 - √5) ^ 2019 ∧ -(2 - √5) ^ 2019 < 1 := by
    have : 2 < √5 := by
      rw [← show √(2^2) = 2 from Real.sqrt_sq (by norm_num), Real.sqrt_lt_sqrt_iff (by norm_num)]
      norm_num
    constructor
    . rw [show 2 - √5 = -1 * (√5 - 2) by ring, mul_pow, Odd.neg_one_pow (by use 1009; norm_num),
      neg_mul, one_mul, neg_neg]
      apply pow_pos
      exact sub_pos.mpr this
    rw [show 2 - √5 = -1 * (√5 - 2) by ring, mul_pow, Odd.neg_one_pow (by use 1009; norm_num),
      neg_mul, one_mul, neg_neg]
    apply pow_lt_one
    . exact sub_nonneg_of_le this.le
    . have : √5 < 1 + 2:= by
        norm_num
        rw [← show √(3^2) = 3 from Real.sqrt_sq (by norm_num), Real.sqrt_lt_sqrt_iff (by norm_num)]
        norm_num
      exact sub_right_lt_of_lt_add this
    . norm_num
  -- So  $\lfloor (2+\sqrt5)^{2019} \rfloor=a_{2019}$ .
  -- Since $a_{2019}$ is even and greater than 2, it cannot be prime.
  rw [← add_sub_cancel_right ((2 + √5) ^ 2019) ((2 - √5) ^ 2019), ← hx, sub_eq_add_neg,
    show (x : ℝ) = ((x : ℤ) : ℝ) by norm_cast, floor_int_add_small _ (by assumption),
    Int.prime_iff_natAbs_prime, Int.natAbs_ofNat, Nat.not_prime_iff_exists_dvd_lt (by linarith)]
  use 2
