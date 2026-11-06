import Mathlib

/- Show that the even integer \( n = 161038 = 2 \cdot 73 \cdot 1103 \) satisfies the congruence \( 2^{n} \equiv 2 \pmod{n} \). The integer 161038 is the smallest even pseudoprime to the base 2.-/
theorem number_theory_4820 {n : ℕ} (hn : n = 161038) : 2^n ≡ 2 [MOD n] := by
  /- 原答案错误，以下为重写的正确证明。 -/
  have nfac : n = 2*73*1103 := by rw [hn]
  have h1co : Nat.Coprime (2*73) 1103 := by decide
  have h2co : Nat.Coprime 2 73 := by decide
  /- 欲证2^n ≡ 2 [MOD n]，只需分别证2^n ≡ 2 [MOD 2]；2^n ≡ 2 [MOD 73]；2^n ≡ 2 [MOD 1103] -/
  rw [nfac, ← Nat.modEq_and_modEq_iff_modEq_mul h1co, ← Nat.modEq_and_modEq_iff_modEq_mul h2co]
  constructor; constructor
  . /- 2^n ≡ 2 [MOD 2] -/
    trans 0
    rw [Nat.modEq_zero_iff_dvd]
    nth_rw 1 [← pow_one 2]
    apply Nat.pow_dvd_pow
    norm_num
    symm
    rw [Nat.modEq_zero_iff_dvd]
  . /- 2^n ≡ 2 [MOD 73] -/
    have h : 2^9 ≡ 1 [MOD 73] := by decide
    rw [show 2*73*1103=9*17893+1 by norm_num, pow_succ]
    nth_rw 3 [← one_mul 2]
    apply Nat.ModEq.mul
    set a := 17893
    have := Nat.ModEq.pow a h
    rwa [one_pow, ← pow_mul] at this
    rfl
  /- 2^n ≡ 2 [MOD 1103] -/
  have h : 2^29 ≡ 1 [MOD 1103] := by decide
  rw [show 2*73*1103=29*5553+1 by norm_num, pow_succ]
  nth_rw 3 [← one_mul 2]
  apply Nat.ModEq.mul
  set a := 5553
  have := Nat.ModEq.pow a h
  rwa [one_pow, ← pow_mul] at this
  rfl
