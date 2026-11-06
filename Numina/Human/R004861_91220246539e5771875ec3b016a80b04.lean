import Mathlib

/- Determine all positive integers $x, y$ and $z$ such that

$$
x^{5}+4^{y}=2013^{z}
$$ -/
theorem number_theory_604305 (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x^5 + 4^y = 2013^z) : False := by

    -- reducing modulo 11 yields x ^ 5 + 4 ^ y ≡ 0 (mod 11)
    have h_mod_11 : x ^ 5 + 4 ^ y ≡ 0 [ZMOD 11] := by
      trans 2013 ^ z
      · norm_cast
        exact congrFun (congrArg HMod.hMod (congrArg Nat.cast h)) 11
      refine Dvd.dvd.modEq_zero_int ?h
      refine Dvd.dvd.pow ?h.hab ?h.x
      norm_num
      exact Nat.not_eq_zero_of_lt hz

    -- note that as 4 ^ 5 ≡ 1 (mod 11), we have 4 ^ y ≡ 4 ^ (y % 5) (mod 11)
    have h_4_pow_y_mod_11 : 4 ^ y ≡ 4 ^ (y % 5) [ZMOD 11] := by
      have : 4 ^ 5 ≡ 1 [ZMOD 11] := by rfl
      have : y = y / 5 * 5 + y % 5 := Eq.symm (Nat.div_add_mod' y 5)
      nth_rw 1 [this]
      rw [pow_add]
      nth_rw 2 [show (4 ^ (y % 5) : ℤ) = 1 * 4 ^ (y % 5) by ring]
      apply Int.ModEq.mul_right
      generalize y / 5 = k
      rw [show (4 : ℤ) ^ (k * 5) = (4 ^ 5) ^ k by rw [mul_comm, pow_mul]]
      trans 1 ^ k
      exact Int.ModEq.pow k (by assumption)
      simp

    -- therefore, enumerating y % 5 we deduce 4 ^ y cannot be eqaul to 0 modulo 11
    have h_4_pow_y_mod_11' : ¬ 4 ^ y ≡ 0 [ZMOD 11] := by
      unfold Int.ModEq
      rw [h_4_pow_y_mod_11]
      have : y % 5 < 5 := by refine Nat.mod_lt y (by norm_num)
      interval_cases y % 5
      all_goals norm_num

    -- as x ^ 5 + 4 ^ y ≡ 0 and 4 ^ y ≠ 0 (mod 11), we cannot have x ^ 5 ≡ 0 (mod 11)
    have : ¬ x ^ 5 ≡ 0 [ZMOD 11] := by
      by_contra! h
      have : 4 ^ y ≡ 0 [ZMOD 11] := by
        trans x ^ 5 + 4 ^ y
        · nth_rw 1 [show (4 : ℤ) ^ y = 0 + 4 ^ y by ring]
          exact Int.ModEq.add (id (Int.ModEq.symm h)) rfl
        exact h_mod_11
      contradiction

    -- by enumerating x % 11, we can only have x ^ 5 ≡ ±1 (mod 11)
    have h_x_pow_5_mod_11_or : x ^ 5 ≡ 1 [ZMOD 11] ∨ x ^ 5 ≡ -1 [ZMOD 11] := by
      unfold Int.ModEq
      have h_x_pow_5_mod_11 : x ^ 5 ≡ (x % 11) ^ 5 [ZMOD 11] := by
        refine Int.ModEq.pow 5 ?_
        exact Int.ModEq.symm (Int.mod_modEq (↑x) 11)
      rw [h_x_pow_5_mod_11]
      have : ↑x % 11 ≥ (0 : ℤ) := Int.emod_nonneg (↑x) (by norm_num)
      have : ↑x % 11 < (11 : ℤ) := by
        apply Int.emod_lt
        norm_num
      interval_cases (x : ℤ) % 11
      · have : x ^ 5 ≡ 0 [ZMOD 11] := by
          unfold Int.ModEq
          rw [h_x_pow_5_mod_11]
          norm_num
        contradiction
      all_goals norm_num

    -- so we have 4 ^ y ≡ ±1 (mod 11)
    have h_4_pow_y_mod_11_or : 4 ^ y ≡ 1 [ZMOD 11] ∨ 4 ^ y ≡ -1 [ZMOD 11]:= by
      have : 4 ^ y ≡ -(x ^ 5) [ZMOD 11] := by
        have := Int.ModEq.sub h_mod_11 (show x ^ 5 ≡ x ^ 5 [ZMOD 11] by rfl)
        simp at this
        exact this
      rcases h_x_pow_5_mod_11_or with h | h
      · right
        trans -(x ^ 5)
        exact this
        exact Int.neg_modEq_neg.mpr h
      · left
        trans -(x ^ 5)
        exact this
        exact Int.neg_modEq_neg.mpr h

    -- again by enumerating y % 11, we cannot have 4 ^ y ≡ -1 (mod 11)
    have h_4_pow_y_mod_11_ne_neg_1 : ¬ 4 ^ y ≡ -1 [ZMOD 11] := by
      unfold Int.ModEq
      rw [h_4_pow_y_mod_11]
      have : y % 5 < 5 := by refine Nat.mod_lt y (by norm_num)
      interval_cases y % 5
      all_goals norm_num

    -- the only remaining case is 4 ^ y ≡ 1 (mod 11)
    have h_4_pow_y_mod_11_eq_1 : 4 ^ y ≡ 1 [ZMOD 11]:= by
      rcases h_4_pow_y_mod_11_or with h | h
      · exact h
      · contradiction

    -- by 4 ^ y ≡ 1 (mod 11) happens only if y % 5 = 0, i.e. 5 ∣ y
    have h_5_dvd_y : 5 ∣ y := by
      suffices h : (5 : ℤ) ∣ y by norm_cast at h
      suffices h : y % (5 : ℤ) = 0 by exact Int.dvd_of_emod_eq_zero h
      have : y % (5 : ℤ) ≥ 0 := Int.emod_nonneg (↑y) (by norm_num)
      have : y % (5 : ℤ) < 5 := by apply Int.emod_lt; norm_num
      interval_cases h : y % (5 : ℤ)
      · rfl
      all_goals
        unfold Int.ModEq at h_4_pow_y_mod_11_eq_1
        norm_cast at h
        rw [h_4_pow_y_mod_11, h] at h_4_pow_y_mod_11_eq_1
        norm_num at h_4_pow_y_mod_11_eq_1

    -- let y = 5 * k, define t = 4 ^ (y/5) = 4 ^ k
    have ⟨k, hk⟩ := h_5_dvd_y
    let t := 4 ^ k

    -- so t ^ 5 = 4 ^ y
    have h_4_pow_y_eq_t_pow_5 : (4 ^ y : ℤ) = t ^ 5 := by
      norm_cast
      unfold t
      rw [← pow_mul, mul_comm, hk]

    -- and the equation becomes x ^ 5 + t ^ 5 = 2013 ^ z
    have h' : x ^ 5 + t ^ 5 = 2013 ^ z := by
      norm_cast at h_4_pow_y_eq_t_pow_5
      rw [← h_4_pow_y_eq_t_pow_5]
      exact h

    -- note that 4 ^ y is even, and 2013 ^ z is odd, we deduce x ^ 5 must be odd
    have h_x_pow_5_odd : Odd (x ^ 5) := by
      by_contra! h_even
      have : Even (x ^ 5) := Nat.not_odd_iff_even.mp h_even
      have : Even (4 ^ y) := by
        refine (Nat.even_pow' ?_).mpr ?_
        exact Nat.not_eq_zero_of_lt hy
        exact Nat.even_iff.mpr rfl
      have : Even (x ^ 5 + 4 ^ y) := by apply Even.add; repeat assumption
      rw [h] at this
      have : Even (2013) := by
        apply Nat.even_pow' (n := z) (by linarith) |>.mp
        exact this
      apply Nat.even_iff.mp at this
      norm_num at this

    -- as odd numbers are coprime to 2, and thus coprime to 4 ^ y
    have lem1 {t : ℤ} : Odd t → IsCoprime t 2 := by
      rintro ⟨h, rfl⟩
      refine IsCoprime.symm (IsCoprime.mul_add_left_right ?intro.h h)
      norm_num

    -- we deduce x ^ 5 and t ^ 5 are coprimes
    have : IsCoprime ((x : ℤ) ^ 5) (t ^ 5) := by
      rw [← h_4_pow_y_eq_t_pow_5]
      apply IsCoprime.pow_right_iff (by linarith) |>.mpr
      rw [show (4 : ℤ) = 2 * 2 by norm_num]
      apply IsCoprime.mul_right_iff.mpr
      constructor
      all_goals
        apply lem1
        norm_cast

    -- therefore, x and t must also be coprime
    have h_coprime_x_t : IsCoprime (x : ℤ) t := IsCoprime.pow_iff
      (show 5 > 0 by norm_num) (show 5 > 0 by norm_num) |>.mp this

    -- we deduce that (t ^ 4) and (x + t) are coprimes
    have h_coprime' : IsCoprime (t ^ 4 : ℤ) (x + t) := by
      refine IsCoprime.pow_left ?_
      refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
      unfold Int.gcd
      rw [Int.natAbs_add_of_nonneg (by linarith) (by linarith)]
      simp
      exact Nat.isCoprime_iff_coprime.mp (id (IsCoprime.symm h_coprime_x_t))

    -- let A = x + t and B = (x ^ 5 + t ^ 5) / (x + t)
    let A : ℤ := x + t
    let B : ℤ := x ^ 4 - x ^ 3 * t + x ^ 2 * t ^ 2 - x * t ^ 3 + t ^ 4

    -- so A * B = x ^ 5 + t ^ 5
    have h_A_mul_B : A * B = x ^ 5 + t ^ 5 := by ring

    -- note that B = A * (x ^ 3 - 2 * x ^ 2 * t + 3 * x * t ^ 2 - 4 * t ^ 3) + 5 * t ^ 4
    have h_B_eq : B = A * (x ^ 3 - 2 * x ^ 2 * t + 3 * x * t ^ 2 - 4 * t ^ 3) + 5 * t ^ 4 := by ring

    -- we need a lemma that gcd(a, a * t + b) = gcd(a, b)
    have lem2 (a b t : ℤ) : Int.gcd a (a * t + b) = Int.gcd a b := by
      have h1 : ↑(Int.gcd a (a * t + b)) ∣ a := Int.gcd_dvd_left
      have h1' : ↑(Int.gcd a (a * t + b)) ∣ a * t := Dvd.dvd.mul_right h1 t
      have h2 : ↑(Int.gcd a (a * t + b)) ∣ a * t + b := Int.gcd_dvd_right
      have h3 : ↑(Int.gcd a (a * t + b)) ∣ b := by
        nth_rw 2 [show b = a * t + b - a * t by ring]
        exact Int.dvd_sub h2 h1'
      have h4 : (Int.gcd a (a * t + b) : ℤ) ∣ Int.gcd a b := Int.dvd_gcd h1 h3
      norm_cast at h4

      have h5 : ↑(Int.gcd a b) ∣ a := Int.gcd_dvd_left
      have h5' : ↑(Int.gcd a b) ∣ a * t := Dvd.dvd.mul_right h5 t
      have h6 : ↑(Int.gcd a b) ∣ a * t + b := by
        refine (Int.dvd_add_right h5').mpr ?_
        exact Int.gcd_dvd_right
      have h7 : (Int.gcd a b : ℤ) ∣ Int.gcd a (a * t + b) := Int.dvd_gcd h5 h6
      norm_cast at h7

      exact dvd_antisymm h4 h7

    -- so gcd(A, B) = gcd(A, A * (x ^ 3 - 2 * x ^ 2 * t + 3 * x * t ^ 2 - 4 * t ^ 3) + 5 * t ^ 4) = gcd(A, 5 * t^4)
    have h_gcd_A_B : Int.gcd A B = Int.gcd A (5 * t ^ 4) := by rw [h_B_eq, lem2]

    -- we cannot have 5 ∣ A, as otherwise 5 ∣ 2013, which is impossible
    -- so we deduce gcd(A, B) = gcd(A, 5 * t^4) = 1
    have : Int.gcd A B = 1 := by
      rw [h_gcd_A_B]
      by_cases h : 5 ∣ A
      · have : 5 ∣ A * B := by exact Dvd.dvd.mul_right h B
        rw [h_A_mul_B] at this
        norm_cast at this
        rw [h'] at this
        have : 5 ∣ (2013 : ℤ) ^ z := by norm_cast
        have := Int.Prime.dvd_pow (show Nat.Prime 5 by norm_num) this
        simp at this
        norm_num at this
      · have h1 : IsCoprime A (t ^ 4) := by
          exact id (IsCoprime.symm h_coprime')
        have h_ir_5 : Irreducible (5 : ℤ) := by
          refine Prime.irreducible ?hp
          norm_num
        have h2 : IsCoprime 5 A := by
          have := dvd_or_coprime 5 A h_ir_5
          rcases this with h' | h'
          · contradiction
          · exact h'
        have : IsCoprime A (5 * t ^ 4) := by
          exact IsCoprime.mul_right (id (IsCoprime.symm h2)) h1
        have : Int.gcd A (5 * t ^ 4) = 1 := Int.isCoprime_iff_gcd_eq_one.mp this
        rw [this]

    -- From A * B = 2013^z and A, B coprime, we get that A = a ^ z and B = b ^ z for some a, b

    have h_unit_gcd_A_B : IsUnit (Int.gcd A B) := by
      rw [this]
      simp

    have h_unit_gcd_B_A : IsUnit (Int.gcd B A) := by
      rw [Int.gcd_comm, this]
      simp

    have h_A_mul_B' : A * B = (2013 : ℤ) ^ z := by
      trans x ^ 5 + t ^ 5
      exact h_A_mul_B
      norm_cast

    have h_A_natabs : A = A.natAbs := by
      exact rfl

    have h_B_natabs: B = B.natAbs := by
      refine Eq.symm (Int.natAbs_of_nonneg ?_)
      have : A * B > 0 := by
        rw [h_A_mul_B']
        simp
      have : A > 0 := by unfold A; norm_cast; linarith
      by_contra! h
      have : A * B < 0 := by exact Int.mul_neg_of_pos_of_neg this h
      linarith

    have h_A_mul_B'' := h_A_mul_B'
    rw [h_A_natabs, h_B_natabs] at h_A_mul_B''
    norm_cast at h_A_mul_B''
    have ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow h_unit_gcd_A_B h_A_mul_B''

    have h_A_mul_B''' := h_A_mul_B'
    rw [h_A_natabs, h_B_natabs, mul_comm] at h_A_mul_B'''
    norm_cast at h_A_mul_B'''
    have ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow h_unit_gcd_B_A h_A_mul_B'''

    have h_A_a : A = a ^ z := by rw [h_A_natabs]; norm_cast
    rw [h_A_a] at h_A_mul_B'

    have h_B_b : B = b ^ z := by rw [h_B_natabs]; norm_cast
    rw [h_B_b] at h_A_mul_B'

    -- so a * b = 2013
    have h_a_mul_b : a * b = 2013 := by
      rw [← mul_pow] at h_A_mul_B'
      norm_cast at h_A_mul_B'
      apply pow_left_inj₀ (n := z) ?_ ?_ ?_ |>.mp
      assumption
      exact Nat.zero_le (a * b)
      norm_num
      linarith

    -- by expanding A ^ 4 we deduce that B ≤ A ^ 4
    have h_B_le_A_pow_4 : B ≤ A ^ 4 := by
      apply le_of_sub_nonneg
      have : A^4 - B = 5 * (x^3*t + x^2*t^2 + x*t^3) := by unfold A B; ring
      rw [this]
      simp
      positivity

    -- this implies b ≤ a ^ 4
    have h_b_le_a_pow_4 : b ≤ a ^ 4 := by
      rw [h_A_a, h_B_b, ← pow_mul, mul_comm, pow_mul] at h_B_le_A_pow_4
      by_contra! h
      have : (a ^ 4) ^ z < b ^ z := by rel [h]
      linarith

    -- and that a ^ 5 ≥ b * a = 2013
    have : a ^ 5 ≥ 2013 := by
      trans a * b
      · rw [mul_comm, pow_succ]
        gcongr
      rw [h_a_mul_b]

    -- this solves to a ≥ 5
    have h_a_ge_5 : a ≥ 5 := by
      by_contra! h
      have : a ^ 5 < 2013 := by
        calc
          a ^ 5 ≤ 4 ^ 5 := by gcongr; exact Nat.le_of_lt_succ h
          _ < 2013 := by norm_num
      linarith

    -- by using the mean inequality (or Jensen's inequality), we deduce that A ^ 5 / 16 ≤ A * B
    have h_A_pow_5_le : A ^ 5 ≤ 16 * A * B := by
      let s : Finset ℕ := {0, 1}
      let f : ℕ → ℝ := fun (n : ℕ) ↦ if n = 0 then x else t
      have hf : ∀ i ∈ s, f i ≥ 0 := by
        intro i
        by_cases h : i = 0
        all_goals simp [h, f]

      have := pow_sum_div_card_le_sum_pow hf 4
      simp [s, f] at this

      have := div_le_iff₀ (show (2 : ℝ) ^ 4 > 0 by norm_num) |>.mp this
      rw [show 2 ^ 4 = (16 : ℝ) by norm_num, mul_comm] at this
      norm_cast at this

      rw [mul_assoc, h_A_mul_B]
      unfold A
      norm_cast

    -- dividing A from both sides, we get A ^ 4 ≤ 16 * B
    have h_A_pow_4_le : A ^ 4 ≤ 16 * B := by
      have : A > 0 := by unfold A; norm_cast; linarith
      apply mul_le_mul_right this |>.mp
      rw [← pow_succ, mul_assoc, show B * A = A * B by ring, ← mul_assoc]
      simp [h_A_pow_5_le]

    -- this implies a ^ 4 ≤ 16 * b
    have h_a_pow_4_le : a ^ 4 ≤ 16 * b := by
      rw [h_A_a, h_B_b, ← pow_mul, mul_comm, pow_mul] at h_A_pow_4_le
      by_contra! h
      have : (a ^ 4) ^ z > 16 * b ^ z := by
        calc
          16 * b ^ z ≤ 16 ^ z * b ^ z := by
            gcongr
            apply le_self_pow₀
            norm_num
            exact Nat.not_eq_zero_of_lt hz
          _ = (16 * b) ^ z := by ring
          _ < (a ^ 4) ^ z := by gcongr
      norm_cast at h_A_pow_4_le
      linarith

    -- so a ^ 5 ≤ 16 * a * b = 16 * 2013
    have h_a_pow_5_le : a ^ 5 ≤ 16 * 2013 := by
      trans 16 * a * b
      · rw [mul_assoc, show a * b = b * a by ring, ← mul_assoc, pow_succ]
        gcongr
      rw [mul_assoc, h_a_mul_b]

    -- this solves to a ≤ 8
    have h_a_le_8 : a ≤ 8 := by
      by_contra! h
      have : a ^ 5 > 16 * 2013 := by
        trans 8 ^ 5
        · gcongr
        norm_num
      linarith

    -- as a * b = 2013, we have a ∣ b
    have h_a_dvd : a ∣ 2013 := by exact Dvd.intro b h_a_mul_b

    -- but there is no factor of 2013 in the interval [5, 8]
    interval_cases a
    all_goals norm_num at h_a_dvd
