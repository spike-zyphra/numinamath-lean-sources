import Mathlib

open ZMod Nat

/-!
# Hundreds Digit of \(N_j = 2^{100j+99} + 2^{100j+100} + 2^{100j+101}\)
We show the hundreds digit of \(N_j\) is always 8 by computing
\(N_j \bmod 8 = 0\) and \(N_j \bmod 125 = 66\),
then assembling by Chinese Remainder.
-/


theorem mod1000_sum (j : ℕ) :
    (2 ^ (100 * j + 99) + 2 ^ (100 * j + 100) + 2 ^ (100 * j + 101) : ZMod 1000) = 816 := by
  -- reduce modulo 8 and 125
  --have h8 := congrArg (fun x : ZMod 1000 => (x : ZMod 8)) (mod8_sum j)
  --have h125 := congrArg (fun x : ZMod 1000 => (x : ZMod 125)) (mod125_sum j)
  -- verify 816 has same residues
  have r8 : (816 : ZMod 8) = 0 := by decide
  have r125 : (816 : ZMod 125) = 66 := by decide

  let val := 2 ^ (100 * j + 99) + 2 ^ (100 * j + 100) + 2 ^ (100 * j + 101)
  let val_mod1000 := (val : ZMod 1000)

  -- rewrite the expression to using `val_mod1000`
  rw [show (2 ^ (100 * j + 99) + 2 ^ (100 * j + 100) + 2 ^ (100 * j + 101) : ZMod 1000) = val_mod1000 by simp [val, val_mod1000]]

  -- Step 1: Apply Chinese Remainder Theorem
  -- It says `ZMod.chineseRemainder` is a bijection
  -- so it is sufficient to show `f val_mod1000 = (0, 66)`
  let f := ZMod.chineseRemainder (by norm_num : Nat.Coprime 8 125)
  apply f.injective

  let val_mod1000_mod8: ZMod 8 := ZMod.cast val_mod1000
  let val_mod_1000_mod125: ZMod 125 := ZMod.cast val_mod1000


  -- Step 2: \(N_j ≡ 0 [MOD 8]\).
  have mod8_sum: (val : ZMod 8) = 0 := by
    have base : (2 : ZMod 8) ^ 3 = 0 := by decide
    have pow_zero : (2 : ZMod 8) ^ (100 * j + 99) = 0 := by
      apply pow_eq_zero_of_le (by norm_num) base

    calc
      _ = (2 ^ (100 * j + 99) + 2 ^ (100 * j + 100) + 2 ^ (100 * j + 101) : ZMod 8) := by simp [val]
      _ =  (7 * 2 ^ (100 * j + 99) : ZMod 8) := by ring
      _ =  7 * 0 := by rw [pow_zero]
      _ =  0 := by ring

  -- Step 3: \(N_j ≡ 66 [MOD 125]\).
  have mod125_sum: (val : ZMod 125) = 66 := by
    -- φ(125)=100 gives 2^100 = 1
    --have one_pow : 2 ^ 100 = 1 := order

    have euler_theorem : 2 ^ 100 ≡ 1 [MOD 125] := by
      rw [show 100 = φ 125 by decide]
      exact Nat.ModEq.pow_totient (by decide: Nat.Coprime 2 125)

    have euler_theorem_zmod : 2 ^ 100 = (1 : ZMod 125) := by
      have h := CharP.natCast_eq_natCast' (ZMod 125) 125 euler_theorem
      have : (2: ZMod 125) ^ 100 = (2 ^ 100 : ℕ) := by norm_cast
      rw [← this] at h
      exact h

    -- (2 ^ 99 : ZMod 125) is the inverse of (2 : ZMod 125)
    have eq_1: (2 ^ 99 : ZMod 125) * (2 : ZMod 125) = 1 := by
      calc
        (2 ^ 99 : ZMod 125) * (2 : ZMod 125) = (2 : ZMod 125) ^ 100 := by ring
        _ = 1 := euler_theorem_zmod

    -- (63: ZMod 125) is the inverse of (2 : ZMod 125)
    have eq_2: (63: ZMod 125) * (2 : ZMod 125) = 1 := by decide

    -- So we have (2 ^ 99 : ZMod 125) = (63: ZMod 125)
    have h_pow_99 : 2 ^ 99 = (63: ZMod 125) := by
      have h : (2 ^ 99 : ZMod 125) * 2 = (63: ZMod 125) * 2 := by
        rw [eq_1, eq_2]

      haveI : Invertible (2 : ZMod 125) := Units.invertible (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 125))

      exact (mul_left_inj_of_invertible (2: ZMod 125)).mp h

    calc
      _ = (2 ^ (100 * j + 99) + 2 ^ (100 * j + 100) + 2 ^ (100 * j + 101) : ZMod 125) := by simp [val]
      _ = (7 * 2 ^ (100 * j + 99) : ZMod 125) := by ring
      _ = 7 * (2 ^ 100) ^ j * 2 ^ 99 := by simp [pow_add, pow_mul, mul_assoc]
      _ = 7 * 1 ^ j * 2 ^ 99 := by rw [euler_theorem_zmod]
      _ = 7 * 2 ^ 99 := by simp
      _ = 7 * 63 := by rw [h_pow_99]
      _ = 66 := by decide

  -- Step 4: Assemble via Chinese Remainder to get 816 mod 1000.

  -- `ZMod.cast_natCast` says `(↑k : ZMod 1000) cast to (↑k : ZMod 8)`
  have val_mod8_eq_0: val_mod1000_mod8 = 0 := by
    have : val_mod1000_mod8 = (val : ZMod 8) := by apply ZMod.cast_natCast (by decide : 8 ∣ 1000)
    rw [mod8_sum] at this
    exact this

  -- `ZMod.cast_natCast` says `(↑k : ZMod 1000) cast to (↑k : ZMod 125)`
  have val_mod125_eq_66: val_mod_1000_mod125 = 66 := by
    have : val_mod_1000_mod125 = (val : ZMod 125) := by apply ZMod.cast_natCast (by decide : 125 ∣ 1000)
    rw [mod125_sum] at this
    exact this

  have rfs: f (816 : ZMod 1000) = ((0 : ZMod 8), (66 : ZMod 125)) := by decide

  have lfs: f val_mod1000 = ((0 : ZMod 8), (66 : ZMod 125)) := by
    -- the bijection in `ZMod.chineseRemainder` is f
    -- by definition, f val_mod1000 = ((val.cast, val.cast): ZMod 8 × ZMod 125)
    have y:f val_mod1000 = (val_mod1000_mod8, val_mod_1000_mod125) := by rfl
    rw [val_mod8_eq_0, val_mod125_eq_66] at y
    exact y

  rw [lfs, rfs]