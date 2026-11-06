import Mathlib

open Nat

/-!
If `N > 35`, `14 ∣ N*(N+1)`, and a natural number `A` satisfies
```lean
A ≡ 35 [MOD N]   -- i.e. N ∣ A - 35
A ≡ 35 [MOD N+1] -- i.e. (N+1) ∣ A - 35
```
then `A ≡ 7 [MOD 14]`.

We break the proof into small lemmas for clarity.
-/

theorem mod14_of_modN_modNplus1 {N A : ℕ}
  (hN_pos : N > 35)
  (h14 : 14 ∣ N * (N + 1))
  (hA_modN   : A ≡ 35 [MOD N])
  (hA_modNp1 : A ≡ 35 [MOD (N + 1)]) :
  A ≡ 7 [MOD 14] := by
  -- Step 1: Extract divisibility from the mod congruences
  have hN_dvd   : (N : ℤ) ∣ A - (35 : ℤ) :=  Nat.modEq_iff_dvd.1 hA_modN.symm
  have hNp1_dvd : ↑(N + 1) ∣ A - (35 : ℤ) := Nat.modEq_iff_dvd.1 hA_modNp1.symm

  -- Step 2: Show gcd(N, N+1) = 1 (consecutive naturals are coprime)
  have hcoprime : Nat.gcd N (N + 1) = 1 := by
    refine (coprime_add_iff_right ?_).mpr ?_
    . exact Nat.dvd_refl N
    . exact Nat.gcd_one_right N

  have h_coprime : IsCoprime (N : ℤ) (N + 1) := Int.isCoprime_iff_gcd_eq_one.mpr hcoprime

  -- Step 3: Use coprimality to lift to divisibility by the product
  have h_prod_dvd : ↑(N * (N + 1)) ∣ A - (35 : ℤ) :=
    IsCoprime.mul_dvd h_coprime hN_dvd hNp1_dvd

  have h14_dvd : (14 : ℤ) ∣ ↑(N * (N + 1)) := Int.ofNat_dvd_right.mpr h14

  -- Step 4: From 14 ∣ N*(N+1) and N*(N+1) ∣ A-35, conclude 14 ∣ A-35
  have h14_dvd : 14 ∣ A - (35 : ℤ) := h14_dvd.trans h_prod_dvd

  -- Step 5: Rewrite as a mod congruence: A ≡ 35 [MOD 14]
  have hA_mod14 : A ≡ 35 [MOD 14] := (Nat.modEq_iff_dvd.2 h14_dvd).symm

  -- Step 6: Note that 35 ≡ 7 [MOD 14]
  have h35_to_7 : 35 ≡ 7 [MOD 14] := by decide

  -- Step 7: Transitivity of congruences yields the result
  exact hA_mod14.trans h35_to_7
