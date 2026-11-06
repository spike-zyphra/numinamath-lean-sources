import Mathlib

/-
Trouver tous les entiers $n \geq 1$ tels que 
\[
6^n - 1 \mid 7^n - 1
\]
-/
theorem number_theory_607380 :
  ¬ ∃ (n : ℕ), (n ≥ 1) ∧  (6 ^ n - 1 : ℤ) ∣ (7 ^ n -1) := by 
  simp 
  intro n hn
  by_contra h
  have dvd1 : (5 : ℤ) ∣ 6 ^ n - 1 := by 
    apply Int.modEq_zero_iff_dvd.mp
    have zmod_aux : 6 ^ n ≡ 1 ^ n [ZMOD 5] := by 
      exact Int.ModEq.pow n rfl
    calc 
      _ ≡  1 ^ n - 1 [ZMOD 5] := by 
        exact Int.ModEq.sub zmod_aux rfl
      _ ≡ 0 [ZMOD 5]:= by norm_num
  have dvd2 : (5 : ℤ) ∣ 7 ^ n - 1 := by 
    exact dvd_trans dvd1 h
  -- analyse the residual of 7 ^ n modulo 5, we get 4 ∣ n
  have mod_aux : ∃ (q : ℕ), n = 4 * q := by 
    -- rw [← Nat.div_add_mod n 4] at dvd2
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, ← ZMod.intCast_zmod_eq_zero_iff_dvd (7^n - 1) 5, ← Nat.div_add_mod n 4, 
    pow_add, pow_mul, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_pow,
    Int.cast_ofNat, show 7 ^ 4 = (1 : ZMod 5) by rfl, one_pow, one_mul, sub_eq_zero] at dvd2
    rw [Int.cast_pow, Int.cast_ofNat, Int.cast_one] at dvd2
    suffices n % 4 = 0 by 
      rw [← Nat.div_add_mod n 4, this]
      use n / 4
      ring_nf
    have mod_lt : n % 4 < 4 := Nat.mod_lt n (by decide)
    interval_cases (n % 4) <;> norm_num at dvd2
    · rfl
    · contradiction
    · contradiction
    · contradiction
  obtain ⟨q, hneq⟩ := mod_aux
  have dvd3 : (7 : ℤ) ∣ 6 ^ n - 1 := by 
    apply Int.modEq_zero_iff_dvd.mp
    have zmod_aux : 6 ^ n ≡ (-1) ^ n [ZMOD 7] := by 
      exact Int.ModEq.pow n rfl
    calc 
      _ ≡ (-1) ^ n - 1 [ZMOD 7] := by 
        exact Int.ModEq.sub zmod_aux rfl
      _ ≡ 0 [ZMOD 7] := by 
        have mod_aux : (-1) ^ n ≡ 1 [ZMOD 7] := by
          rw [hneq]
          have eq_aux : (-1) ^ (4 * q) = 1 := by 
            refine Even.neg_one_pow ?_
            refine Nat.even_mul.mpr ?_
            left 
            unfold Even
            use 2
          rw [eq_aux]
        exact Int.ModEq.sub mod_aux rfl
  have not_dvd : ¬ (7 : ℤ) ∣ 7 ^ n - 1 := by 
    have dvd_aux : (7 : ℤ) ∣ 7 ^ n := by 
      norm_cast
      refine dvd_pow ?_ ?_
      omega
      omega
    omega
  have dvd4 : (7 : ℤ) ∣ 7 ^ n - 1 := dvd_trans dvd3 h
  exact not_dvd dvd4


