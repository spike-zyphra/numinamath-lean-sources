import Mathlib

/- Find $9^{-1} \pmod{100}$, as a residue modulo 100.  (Give an answer between 0 and 99, inclusive.) -/
theorem number_theory_23378 :
  ∀x:ℤ, x*9 ≡ 1 [ZMOD 100] → x ≡ 89 [ZMOD 100] := by
  intro x hx
  -- notice that 9*11=99 ≡ -1 (mod 100), so 9 * -11 ≡ 1 mod 100
  have h1: -11 * 9 ≡ 1 [ZMOD 100] := by
    norm_num; rfl
  -- and -11 ≡ 89 mod 100, so 89 also works. answer is 89
  have h2: 89*9 ≡ 1 [ZMOD 100] := by
    have: 89*9 = -11*9+100*9 := by norm_num
    rw [this]
    apply Int.modEq_add_fac 9 h1
  -- so x is 89, or x ≡ 89 mod 100
  have h3: x*9 ≡ 89*9 [ZMOD 100] := by
    apply Int.ModEq.trans hx h2.symm
  have h4: 100 ∣ 9*(x-89) := by
    have: 9*(x-89) = x*9-89*9 := by ring
    rw [this]
    exact Int.ModEq.dvd h3.symm
  -- 9 and 100 are coprime, so we have 100 ∣ x-89
  have h5: 100 ∣ x-89 := by
    have: Int.gcd 100 9 = 1 := by norm_num
    exact Int.dvd_of_dvd_mul_right_of_gcd_one h4 this
  apply Int.modEq_iff_dvd.mpr
  exact dvd_sub_comm.mp h5