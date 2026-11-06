import Mathlib
set_option exponentiation.threshold 9999999
/-!
Let `F` be the Fermat prime `2^(2^m) + 1`. And `m + 1 ≤ 1989`.
Show that `F` divides `2^(2^1989) - 1`.
-/
theorem Fermat_divides
  {m : ℕ} (hprime : (2 ^ (2 ^ m) + 1).Prime) (hle : m + 1 ≤ 1989) :
  (2 ^ (2 ^ m) + 1) ∣ (2 ^ (2 ^ 1989) - 1) := by
  -- Let F := 2^(2^m) + 1, our Fermat prime
  let F := 2 ^ (2 ^ m) + 1
  have hF : F ≠ 0 := by
    -- F > 1, since it's prime
    have : 1 < F := by
      simp [F]
    omega

  have h_F_eq_zero_mod_F : (F : ZMod F) = 0 := by exact ZMod.natCast_self F

  have h_F_ge_1 : 1 ≤ F := by simp [F]

  -- 1. Show 2^(2^m) ≡ -1 [ZMOD F]
  have fundamental : (2 ^ (2 ^ m) : ZMod F) = -1 := by
    calc (2 ^ (2 ^ m) : ZMod F)
        _ = (F - 1 : ZMod F) := by
          -- by definition F = 2^(2^m) + 1
          simp only [F]
          norm_cast
        _ = -1 := by simp [h_F_eq_zero_mod_F]

  -- 2. Square to get 2^(2^(m+1)) ≡ 1 [ZMOD F]
  have h_pow_two : (2 ^ (2 ^ (m + 1)) : ZMod F) = 1 := by
    have h1 : 2 ^ (m + 1) = 2 ^ m * 2 := by simp [pow_succ]
    have h2 : (2 : ZMod F) ^ (2 ^ (m + 1)) = ((2 : ZMod F) ^ (2 ^ m)) ^ 2 := by
      rw [h1, pow_mul]
    rw [h2, fundamental]
    simp


  -- 3. Raise this to the remaining exponent
  have big_pow : (2 ^ (2 ^ 1989) : ZMod F) = 1 := by
    have h1: 1989 = (m + 1) + (1989 - (m + 1)):= by omega
    have h2: 1989 - (m + 1) = 1988 - m := by omega
    calc (2 ^ (2 ^ 1989) : ZMod F)
          = (2 : ZMod F) ^ (2 ^ (m + 1) * 2 ^ (1989 - (m + 1))) := by
          have : 2 ^ 1989 = 2 ^ (m + 1) * 2 ^ (1989 - (m + 1)) := by
            rw [← pow_add]
            congr
          rw [this]
        _ = ((2 : ZMod F) ^ (2 ^ (m + 1))) ^ (2 ^ (1989 - (m + 1))) := by simp [pow_mul]
        _ = 1 ^ (2 ^ (1989 - (m + 1))) := by simp [h_pow_two]
        _ = 1 := by simp

  -- 4. Conclude divisibility: F ∣ (2^(2^1989) - 1)
  have h_big_pow : (2 ^ (2 ^ 1989) : ZMod F) - 1 = 0 := by rw [big_pow]; simp

  have h_pow_two_ge_zero : 0 < 2 ^ 1989  := (pow_pos_iff (by norm_num: 1989 ≠ 0)).mpr (by norm_num: 2 > 0)

  have h_pow_two_ne_zero : 2 ^ 1989 ≠ 0 := by exact pow_ne_zero 1989 (by decide: 2 ≠ 0)

  rw [← CharP.cast_eq_zero_iff (ZMod F), Nat.cast_sub, Nat.cast_pow]
  . exact h_big_pow
  . exact (pow_pos_iff h_pow_two_ne_zero).mpr (by norm_num: 2 > 0)
