import Mathlib



/--
Theorem:
Let b ≠ 0 in ℤ and n > 0 in ℕ.
If b * n ∣ 2^n - 2, then (2^n - 1) ∣ (2^(2^n - 1) - 2).
-/
theorem divisibility_theorem (b : ℤ) (hb : b ≠ 0) (n : ℕ) (hn : n > 0)
  (hbn : (b * n) ∣ (2^n - 2)) :
  (2^n - 1) ∣ (2^(2^n - 1) - 2) := by

  if hn_eq_1 : n = 1 then
    -- If n = 1, the hypothesis becomes b ∣ 2¹ - 2 = 0, which is always true for b ≠ 0.
    -- The goal becomes 2¹ - 1 ∣ 2^(2¹⁻¹) - 2, which simplifies to 1 ∣ 2¹ - 2, so 1 ∣ 0.
    -- This is also always true.
    simp [hn_eq_1]
  else
    -- Step 1: work modulo m = 2^n - 1
    let m := 2^n - 1
    -- in ZMod m, 2^n ≡ 1
    have pow_eq : (2 : ZMod m)^n = 1 := by
      -- 2^n = m + 1 by definition
      have : 2 ^ n = m + 1 := by exact Eq.symm (succ_mersenne n)
      norm_cast
      rw [this]
      simp

    have h_pow_ge_2 : 2 ^ n ≥ 2 := by
        calc
          2 ^ n ≥ 2 ^ 2 := by
            gcongr
            linarith
            omega
          _     ≥ 2     := by norm_num


    -- define the order r = ord_m(2)
    let r := orderOf (2 : ZMod m)
    -- r ∣ n because 2^n ≡ 1
    have h_r_dvd_n : r ∣ n := by
        -- We show that (2 : ZMod m)ⁿ = 1.
        have h_2_pow_n_mod_m : (2 : ZMod m) ^ n = 1 := by
          -- This holds because 2ⁿ = m + 1.
          have h_pow_eq_m_plus_1 : 2 ^ n = m + 1 := by exact Eq.symm (succ_mersenne n)
          calc
            (2 : ZMod m) ^ n = ↑(2 ^ n)   := by rfl
            _                = ↑(m + 1)   := by
              norm_cast
              rw [show 2 ^ n = m + 1 by omega]
            _                = 1          := by simp [m]
        -- By the properties of order, if 2ⁿ ≡ 1, then the order must divide n.
        exact orderOf_dvd_of_pow_eq_one h_2_pow_n_mod_m

    -- Step 2: from b * n ∣ 2^n - 2 we get n ∣ 2^n - 2
    have h_n_dvd_nat : n ∣ 2 ^ n - 2 := by
        -- First, establish the divisibility in ℤ using a `calc` block for transitivity.
        have h_n_dvd_int : (n : ℤ) ∣ ↑(2 ^ n - 2) := by
          calc
            (n : ℤ) ∣ b * ↑n         := Int.dvd_mul_left b ↑n
            _       ∣ (2 ^ n : ℤ) - 2  := hbn

        -- Now, convert the divisibility from ℤ to ℕ.
        -- This requires `2ⁿ ≥ 2`, which is true for n > 1.
        have h_pow_ge_2 : 2 ^ n ≥ 2 := by
          calc
            2 ^ n ≥ 2 ^ 2 := by
              gcongr
              linarith
              omega
            _     ≥ 2     := by norm_num

        -- -- `↑a ∣ ↑b` in ℤ implies `a ∣ b` in ℕ.
        zify
        rw [show ((2:ℤ) ^ n) - ↑2 = ↑((2:ℕ) ^ n - (2:ℕ)) from by norm_cast] at h_n_dvd_int
        exact h_n_dvd_int

    -- Step 3: r ∣ 2^n - 2 by transitivity
    have hr_div : r ∣ (2^n - 2) := Nat.dvd_trans h_r_dvd_n h_n_dvd_nat

    -- Step 4: write 2^n - 2 = r * ℓ and compute
    obtain ⟨ℓ, hℓ⟩ := exists_eq_mul_left_of_dvd hr_div

    have h_pow_eq : (2^(2^n - 1) : ZMod m) = 2 * (2^(2^n - 2) : ZMod m) := by
      -- rewrite the exponent as a sum
      have : 2^n - 1 = (2^n - 2) + 1 := by omega
      -- now apply `pow_add` and `pow_one`
      rw [this, pow_add, pow_one]
      -- in ZMod, `2 * 2^(2^n - 2)` is definitionally the right-hand side
      ring

    have h_order_eq: 2 ^ r = (1 : ZMod m) := by exact pow_orderOf_eq_one (2 : ZMod m)

    -- show 2^(2^n - 1) ≡ 2 mod m
    have sub_eq_zero : (2^(2^n - 1) - 2 : ZMod m) = 0 := by
      have: (2^(2^n - 1) : ZMod m) = (2 : ZMod m) := by
        calc
          _ = 2 * 2^(2^n - 2) := h_pow_eq
          _ = 2 * 2^(r * ℓ) := by simp [hℓ, mul_comm]
          _ = 2 * (2 ^ r) ^ ℓ          := by ring
          _ = 2 * 1 ^ ℓ                := by simp [h_order_eq]
          _ = (2 : ZMod m)            := by simp
      exact sub_eq_zero_of_eq this

    have h_le_sub : 2 ≤ 2 ^ (2 ^ n - 1) := by
      calc
        2 = 2 ^ 1             := by rw [pow_one]
        _ ≤ 2 ^ (2 ^ n - 1)   := by gcongr <;> omega

    rw [← CharP.cast_eq_zero_iff (ZMod m), Nat.cast_sub, Nat.cast_pow]
    . exact sub_eq_zero
    . exact h_le_sub
