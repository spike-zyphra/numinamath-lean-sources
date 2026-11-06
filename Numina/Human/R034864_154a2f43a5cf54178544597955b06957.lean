import Mathlib

/- Let $a, b$ be two integers coprime with $n$. We denote $\omega(a)$ and $\omega(b)$ as the respective orders of $a$ and $b$ modulo $n$. We assume that $\omega(a)$ and $\omega(b)$ are coprime. What is the order of $a b$ modulo $n$? -/
theorem number_theory_136150 {a b n ωa ωb : ℕ} (ha : Nat.Coprime a n) (hb : Nat.Coprime b n)
    (hωa : ωa = orderOf (a : ZMod n)) (hωb : ωb = orderOf (b : ZMod n)) (hcoprime : Nat.Coprime ωa ωb) :
    orderOf ((a * b) : ZMod n) = ωa * ωb := by
  /- three lines proof using an existing lemma Commute.orderOf_mul_eq_mul_orderOf_of_coprime
    subst ωa ωb
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime _ hcoprime]
    rw [commute_iff_eq, mul_comm] -/
  -- prove an auxiliary lemma that 0 < orderOf (x : ZMod n) for any x coprime with n
  have hpos {x : ℕ} (hx : x.Coprime n) : 0 < orderOf (x : ZMod n) := by
    have hu : IsUnit (x : ZMod n) := (ZMod.isUnit_iff_coprime x n).mpr hx
    have eq : orderOf hu.unit = orderOf (x : ZMod n) := by
      rw [←orderOf_units, hu.unit_spec]
    rw [←eq]
    exact orderOf_pos _
  subst ωa ωb
  have ha0 := hpos ha
  have hb0 := hpos hb
  -- show that orderOf (a * b) ≤ orderOf a * orderOf b and
  -- orderOf a * orderOf b ≤ orderOf (a * b)
  apply eq_of_le_of_le
  · apply orderOf_le_of_pow_eq_one (mul_pos ha0 hb0)
    -- to show that orderOf (a * b) ≤ orderOf a * orderOf b,
    -- it is enought to prove that (a * b) ^ (orderOf a * orderOf b) = 1
    rw [mul_pow, pow_mul, pow_orderOf_eq_one]
    rw [pow_mul', pow_orderOf_eq_one, one_pow, one_pow, mul_one]
  -- to show that orderOf a * orderOf b ≤ orderOf (a * b),
  -- provate that orderOf a * orderOf b ∣ orderOf (a * b)
  · apply Nat.le_of_dvd
    · norm_cast
      apply hpos
      exact Nat.Coprime.mul ha hb
    -- we have orderOf x divides orderOf (x * y) when orderOf x is coprime with orderOf y
    have h {x y : ℕ} (ho : Nat.Coprime (orderOf (x : ZMod n)) (orderOf (y : ZMod n))) :
        orderOf (x : ZMod n) ∣ orderOf (x * y : ZMod n) := by
      -- orderOf x | orderOf (x * y) ↔ orderOf x ∣ orderOf (x * y) * orderOf y
      -- (since orderOf x and orderOf y are coprime)
      apply ho.dvd_of_dvd_mul_left
      -- it is enough to show that x ^ (orderOf (x * y) * orderOf y) = 1
      rw [orderOf_dvd_iff_pow_eq_one]
      symm
      -- we have
      -- 1 = (x * y) ^ (orderOf (x * y) * orderOf y)
      --   = x ^ (orderOf (x * y) * orderOf y) * (y ^ orderOf y) ^ orderOf (x * y)
      --   = x ^ (orderOf (x * y) * orderOf y) * 1
      calc
        1 = (x * y : ZMod n) ^ (orderOf (x * y : ZMod n) * orderOf (y : ZMod n)) := by
            rw [pow_mul, pow_orderOf_eq_one, one_pow]
        _ = x ^ (orderOf (y : ZMod n) * orderOf (x * y : ZMod n)) := by
            rw [mul_pow, mul_comm, mul_comm (orderOf _) _, pow_mul, pow_orderOf_eq_one, one_pow, one_mul]
    -- we get orderOf a ∣ orderOf (a * b) and orderOf b ∣ orderOf (a * b)
    -- orderOf a and orderOf b are coprime, so orderOf a * orderOf b ∣ orderOf (a * b)
    apply hcoprime.mul_dvd_of_dvd_of_dvd (h hcoprime)
    rw [mul_comm]
    exact h (Nat.coprime_comm.mp hcoprime)