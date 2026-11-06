import Mathlib

/- Given $m\geq 2$, denote by $b^{-1}$ the inverse of $b\pmod{m}$.
That is, $b^{-1}$ is the residue for which $bb^{-1}\equiv 1\pmod{m}$.
Sadie wonders if $(a+b)^{-1}$ is always congruent to $a^{-1}+b^{-1}$ (modulo $m$).
She tries the example $a=2$, $b=3$, and $m=7$.
Let $L$ be the residue of $(2+3)^{-1}\pmod{7}$,
and let $R$ be the residue of $2^{-1}+3^{-1}\pmod{7}$,
where $L$ and $R$ are integers from $0$ to $6$ (inclusive). Find $L-R$. -/
theorem number_theory_19209 {m : ℕ} (hm : m = 7)
  (a b : ZMod m) (ha : a = 2) (hb : b = 3) :
  ((a + b)⁻¹ : ZMod m) - (a⁻¹ + b⁻¹ : ZMod m) = 1 := by
  -- a+b=5, inverse of 5 mod 7 is 3.
  have h1: (a+b)⁻¹ = 3 := by
    rw [ha, hb]; norm_num
    apply ZMod.inv_eq_of_mul_eq_one m
    -- 15 mod 7 is 1.
    norm_num
    have hh1: 15 ≡ 1 [MOD m] := by
      rw [hm]; rfl
    have hh2 := (ZMod.natCast_eq_natCast_iff 15 1 m).mpr hh1
    simp at hh2
    exact hh2
  -- a=2, inverse of 2 mod 7 is 4.
  have h2: a⁻¹ = 4 := by
    rw [ha]
    apply ZMod.inv_eq_of_mul_eq_one m
    norm_num
    have hh1: 8 ≡ 1 [MOD m] := by
      rw [hm]; rfl
    have hh2 := (ZMod.natCast_eq_natCast_iff 8 1 m).mpr hh1
    simp at hh2
    exact hh2
  -- b=3, inverse of 3 mod 7 is 5.
  have h3: b⁻¹ = 5 := by
    rw [hb]
    apply ZMod.inv_eq_of_mul_eq_one m
    norm_num
    have hh1: 15 ≡ 1 [MOD m] := by
      rw [hm]; rfl
    have hh2 := (ZMod.natCast_eq_natCast_iff 15 1 m).mpr hh1
    simp at hh2
    exact hh2
  -- a⁻¹+ b⁻¹ mod 7 is 2
  have h4: a⁻¹ + b⁻¹ = 2 := by
    rw [h2, h3]; norm_num
    have hh1: 9 ≡ 2 [MOD m] := by
      rw [hm]; rfl
    have := (ZMod.natCast_eq_natCast_iff 9 2 m).mpr hh1
    simp at this; exact this
  -- we get the result.
  rw [h1,h4]
  norm_num