import Mathlib

open Nat
open ZMod


/--
Let `p` be an odd prime. Then `(p - 3)! ≡ (p - 1)/2 [MOD p]`.
This is a consequence of Wilson's Theorem: (p-1)! ≡ -1 [MOD p].
-/
theorem factorial_mod_half (p : ℕ) [hp : Fact p.Prime] (hp_ge3 : 3 ≤ p) :
    ((p - 3)! : ZMod p) = (p - 1) / 2 := by

  have hp_prime : Nat.Prime p := Fact.out

  have not_dvd : ¬ p ∣ 2 := by
    refine not_dvd_of_pos_of_lt ?_ hp_ge3
    norm_num

  have h_even : Even (p - 1) := by
    refine Prime.even_sub_one hp_prime ?_
    omega

  have h_odd_p: Odd p := by
    refine Nat.Prime.odd_of_ne_two hp_prime ?_
    omega


  -- Step 1: Wilson's Theorem: (p - 1)! ≡ -1 mod p
  have h_wilson : ((p - 1)! : ZMod p) = -1 := by
    exact ZMod.wilsons_lemma p

  -- Step 2: Expand (p - 1)! = (p - 1)(p - 2)(p - 3)!

  have h_nat : (p - 1)! = (p - 1) * (p - 2) * (p - 3)! := by
    calc
      _ = (p - 1) * (p - 2)! := by
          have : p - 2 + 1 = p - 1 := by omega
          rw [← this, Nat.factorial_succ (p - 2)]
      _ = (p - 1) * (p - 2) * (p - 3)! := by
          have : p - 3 + 1 = p - 2 := by omega
          rw [← this, Nat.factorial_succ (p - 3)]
          exact Eq.symm (Nat.mul_assoc (p - 1) (p - 3 + 1) (p - 3)!)

  -- So in ZMod p: (p - 1 : ℤ/p) * (p - 2 : ℤ/p) * (p - 3)! = -1
  have : ((p - 1)! : ZMod p) = ((p - 1) : ZMod p) * ((p - 2) : ZMod p) * ((p - 3)! : ZMod p) := by
    rw [h_nat, Nat.cast_mul, Nat.cast_mul]
    congr
    . exact_mod_cast (Nat.cast_sub (by omega : 1 ≤ p))
    . exact_mod_cast (Nat.cast_sub (by omega : 2 ≤ p))

  have h1 : ((p - 1) : ZMod p) = -1 := by simp
  have h2 : ((p - 2) : ZMod p) = -2 := by simp

  rw [h_wilson, h1, h2] at this

   -- We now have 2 * (p-3)! = -1, so (p-3)! = -1/2 = (p-1)/2
  have h_two_ne_zero : (2 : ZMod p) ≠ 0 := by
    refine Ring.two_ne_zero ?_
    have : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
    rw [this]
    omega

  -- Now we have (-1) * (-2) * (p-3)! = -1
  have h_eq: (2 : ZMod p) * ((p - 3)! : ZMod p) = -1 := by
    convert this.symm using 1
    ring

  have h_eq: (-2 : ZMod p) * ((p - 3)! : ZMod p) = 1 := by
    calc
      _ = (-2 : ZMod p) * ((p - 3)! : ZMod p) := by ring
      _ = (-1 : ZMod p) * (2 : ZMod p) * ((p - 3)! : ZMod p) := by ring
      _ = (-1 : ZMod p) * (-1 : ZMod p) := by rw [mul_assoc, h_eq]
      _ = (1 : ZMod p) := by ring

  -- prove (p - 3)! = (-2)⁻¹
  have h_inv : ((p - 3)! : ZMod p) = ((-2 : ZMod p)⁻¹ : ZMod p) := Eq.symm (ZMod.inv_eq_of_mul_eq_one p (-2) (↑(p - 3)!) h_eq)

  have h_eq': (-2 : ZMod p) * ((p - 1) / 2 : ZMod p) = 1 := by
    have: 2 * ((p - 1: ℤ) / 2: ℤ) = (p - 1: ℤ) := by
      have h_even_int : Even (p - 1 : ℤ) := by
        refine Int.even_sub_one.mpr ?_
        refine Int.not_even_iff_odd.mpr ?_
        refine (Int.odd_coe_nat p).mpr ?_
        exact h_odd_p
      exact Int.two_mul_ediv_two_of_even h_even_int

    let a: ℤ := -2
    let b: ℤ := (p - 1) / 2
    let c: ℤ := 1 - p

    let ma: ZMod p := a
    let mb: ZMod p := b
    let mc: ZMod p := c

    have h_eq: a * b = c := by omega

    have h_eq_mod_p: ma * mb = mc := by
      simp only [ma, mb, mc]
      rw [← Int.cast_mul]
      exact congr_arg Int.cast h_eq

    have: mc = (1: ZMod p) := by calc
      _ = (1: ZMod p) - (p : ZMod p) := by simp [mc, c]
      _ = 1 := by simp

    simp [ma, mb, h_eq_mod_p, this]
    ring_nf
    exact inv_mul_cancel₀ h_two_ne_zero

  -- prove (p - 1) / 2 = (-2)⁻¹
  have h_inv': ((p - 1) / 2 : ZMod p) = ((-2 : ZMod p)⁻¹ : ZMod p) := Eq.symm (ZMod.inv_eq_of_mul_eq_one p (-2) ((↑p - 1) / 2) h_eq')

  rw [h_inv', h_inv]
