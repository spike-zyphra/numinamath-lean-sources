import Mathlib

/-!
  Let \(K\) be a positive even integer, and let \(p\) be a prime with \(p \equiv 3 \pmod{4}\).
  If \(p \mid a^K + b^K\), then \(p \mid a\) and \(p \mid b\).
-/
open Nat

theorem prime_dvd_even_pow_sum
  {p K a b : ℕ}
  (hp : Nat.Prime p)
  (hmod4 : p % 4 = 3)
  (hK : ∃ m > 0, K = 2 * m)
  (hdvd : p ∣ a ^ K + b ^ K) :
  p ∣ a ∧ p ∣ b := by
  -- Extract `m` from the fact that `K` is even.
  obtain ⟨m, h⟩ := hK
  have hm : m > 0 := h.1
  have hK : K = 2 * m := h.2
  -- Now the hypothesis is `p ∣ a^(2*m) + b^(2*m)`, i.e.
  have hsum : p ∣ (a ^ (2 * m) + b ^ (2 * m)) := by
    rw [← hK]
    exact hdvd

  haveI : Fact (Nat.Prime p) := ⟨hp⟩

  -- Case 1: `p ∣ b`.
  by_cases hb : p ∣ b
  · -- If `p ∣ b`, then `p ∣ b^(2*m)`. From `p ∣ a^(2*m) + b^(2*m)` we deduce `p ∣ a^(2*m)`.
    have h1 : p ∣ b ^ (2 * m) := by
      apply dvd_pow hb
      omega
    have hsum' : p ∣ a ^ (2 * m) := by
      -- `a^(2*m) = (a^(2*m) + b^(2*m)) - b^(2*m)`.
      exact (Nat.dvd_add_iff_left h1).mpr hsum
    -- Since `p` is prime and divides `a^(2*m)`, it must divide `a`.
    have ha : p ∣ a := Nat.Prime.dvd_of_dvd_pow hp hsum'
    exact ⟨ha, hb⟩

  · -- Case 2: `p ∤ b`. Then in `ZMod p`, the element `b` is a unit (invertible).
    have hbZ : (b : ZMod p) ≠ 0 := by
      -- If `(b : ZMod p) = 0`, then `p ∣ b`. Contradiction with `hb`.
      intro h0
      have : p ∣ b := by
        exact (ZMod.natCast_zmod_eq_zero_iff_dvd b p).mp h0
      exact hb this

    -- Consider the equation `a^(2*m) + b^(2*m) ≡ 0 (mod p)`.
    -- In `ZMod p`, that is `(a^(2*m) : ZMod p) + (b^(2*m) : ZMod p) = 0`.
    have hZ : (a ^ (2 * m) : ZMod p) + (b ^ (2 * m) : ZMod p) = 0 := by
      -- `p ∣ a^(2*m) + b^(2*m)` implies `(a^(2*m) + b^(2*m) : ZMod p) = 0`.
      simp only [← Nat.cast_add, ← Nat.cast_pow]
      exact (ZMod.natCast_zmod_eq_zero_iff_dvd (a ^ (2 * m) + b ^ (2 * m)) p).mpr hsum

    -- Rewrite `a^(2*m) + b^(2*m) = 0` as `(a^m)^2 + (b^m)^2 = 0`.
    have hSquares : ( (a ^ m : ZMod p) ^ 2 + (b ^ m : ZMod p) ^ 2 ) = 0 := by
      -- In `ZMod p`, `a^(2*m) = (a^m)^2` and likewise for `b`.
      convert hZ using 1
      simp only [← pow_mul, mul_comm]

    -- Hence `(a^m : ZMod p)^2 = -(b^m : ZMod p)^2`. Since `b^m` is a unit in `ZMod p`,
    -- we can multiply by `(b^m)⁻²` to see `((a^m)*(b^m)⁻¹)^2 = -1` in `ZMod p`.
    have hb_unit : IsUnit (b ^ m : ZMod p) := by
      -- If `b` is a unit, then so is any power of `b`.
      have b_unit : IsUnit (b : ZMod p) := by
        refine (ZMod.isUnit_iff_coprime b p).mpr ?_
        exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb)
      exact IsUnit.pow m b_unit
    let r := (a ^ m : ZMod p) * (b ^ m : ZMod p)⁻¹
    have hr : r ^ 2 = -1 := by
      calc
        r ^ 2
            = ( (a ^ m : ZMod p) ^ 2 * ( (b ^ m : ZMod p)⁻¹ ) ^ 2 ) := by
          rw [mul_pow]
        _ = (a ^ m : ZMod p) ^ 2 * ( (b ^ m : ZMod p) ^ 2 )⁻¹  := by rw [inv_pow]
        _ = -1 := by
          -- Use (a^m)^2 + (b^m)^2 = 0 to get (a^m)^2 = -(b^m)^2
          have : (a ^ m : ZMod p) ^ 2 = -(b ^ m : ZMod p) ^ 2 := by apply Eq.symm (neg_eq_of_add_eq_zero_left hSquares)
          simp [this, mul_inv_cancel₀, IsUnit.ne_zero hb_unit]


    -- At this point we have an element `r : ZMod p` with `r^2 = -1`. We show that is impossible
    -- for a prime `p ≡ 3 [MOD 4]`.
    have neg_one_not_square : ¬ ∃ (x : ZMod p), x ^ 2 = -1 := by
      by_contra hcontra
      obtain ⟨x, hx⟩ := hcontra
      -- Fermat's little theorem in `ZMod p`: `x^(p-1) = 1`.
      have fle : x ^ (p - 1) = 1 := by
        apply ZMod.pow_card_sub_one_eq_one
        intro h0
        rw [h0] at hx
        simp at hx

      -- But also `(x^2)^((p-1)/2) = x^(p-1)`. Since `x^2 = -1`, we get `(-1)^((p-1)/2)`.
      have pow_eq : x ^ (p - 1) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
        have hdiv : 2 * ((p - 1) / 2) = p - 1 := by
          have : (p - 1) % 2 = 0 := by
            calc
              (p - 1) % 2 = (p % 2 + (2 - 1)) % 2 := by simp;omega
              _ = (1 + 1) % 2 := by simp;omega
              _ = 0 := by norm_num
          exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero this)
        calc
          x ^ (p - 1) = x ^ (2 * ((p - 1) / 2)) := by rw [hdiv]
          _ = (x ^ 2) ^ ((p - 1) / 2) := pow_mul _ _ _
          _ = (-1) ^ ((p - 1) / 2) := by rw [hx]
      -- Combine them: `1 = (-1) ^ ((p - 1) / 2)`.
      have eq1 : 1 = (-1 : ZMod p) ^ ((p - 1) / 2) :=
        Eq.trans fle.symm pow_eq
      -- But if `p ≡ 3 [MOD 4]`, then `(p - 1) / 2` is odd, so `(-1)^odd = -1 ≠ 1`.
      have parity : ¬ Even ((p - 1) / 2) := by
        -- `p % 4 = 3` means `p = 4k + 3` for some `k`, so `p - 1 = 4k + 2`, hence `(p - 1)/2 = 2k + 1` is odd.
        obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 3 := by
          use p / 4
          rw [← Nat.div_add_mod p 4, hmod4]
          omega

        have hpn : p - 1 = 4 * k + 2 := by simp [← hk]
        have : (p - 1) / 2 = 2 * k + 1 := by
          rw [hpn]
          omega
        simp [this, Nat.not_even_iff]
      -- Thus `(-1)^((p - 1)/2) = -1`. Contradiction to `eq1`.
      have ne : (-1 : ZMod p) ^ ((p - 1) / 2) = -1 := by
        -- Use fact that (-1)^n = -1 when n is odd
        have : Odd ((p - 1) / 2) := by exact not_even_iff_odd.mp parity
        exact Odd.neg_one_pow this

      have : (1 : ZMod p) = -1 := Eq.trans eq1 ne
      -- For an odd prime p, 1 ≠ -1 in ZMod p since p > 2
      have h_ne : (1 : ZMod p) ≠ -1 := by
        have thi: p ≠ 2 := by
          -- p ≡ 3 (mod 4) implies p ≠ 2 since 2 ≡ 2 (mod 4)
          intro h2
          rw [h2] at hmod4
          norm_num at hmod4
        intro h
        have h2 : (2 : ZMod p) = 0 := by
          -- We can rewrite the goal using our assumption `h`.
          -- Adding 1 to both sides of `1 = -1` gives `1 + 1 = -1 + 1`, which simplifies to `2 = 0`.
          calc
            (2 : ZMod p) = 1 + 1 := by ring
            _ = -1 + 1 := by 
              exact congrFun (congrArg HAdd.hAdd this) 1
            _ = 0       := by ring

        -- The statement `(2 : ZMod p) = 0` means that p divides 2.
        have h_dvd : p ∣ 2 := by
          -- ZMod.nat_cast_eq_zero_iff_dvd is the lemma that connects casting to 0 and divisibility.
          rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
          exact h2

        -- Since p is a prime number that divides 2, it must be 2.
        have h_p_eq_2 : p = 2 := by
          -- The divisors of 2 are 1 and 2.
          -- A prime number is by definition greater than or equal to 2.
          -- Therefore, p must be 2.
          have : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).mp h_dvd
          exact this.resolve_left hp.ne_one

        exfalso
        omega

      exact h_ne this

    -- Applying the contradiction `neg_one_not_square` to witness that `r^2 = -1` is impossible.
    have : False := neg_one_not_square ⟨r, hr⟩
    contradiction
