import Mathlib

/- a) \(7 x \equiv 12 \pmod{17}\)-/
theorem number_theory_4785_1 (x : ℕ) : 7 * x ≡ 12 [MOD 17] ↔ x ≡ 9 [MOD 17] := by
  simp [← ZMod.eq_iff_modEq_nat]
  constructor
  . intro h
    -- multiple 5 at both side of h
    apply_fun ((5 : ZMod 17) * ·) at h
    -- conclude x=9 mod 17 by simple calculation
    rwa [← mul_assoc, show 5*7=(1 : ZMod 17) from rfl, show 5*12=(9 : ZMod 17) from rfl, one_mul] at h
  -- verify the answer is correct
  . intro h
    rw [h]
    rfl

/- b) \(4 x \equiv 11 \pmod{19}\)-/
theorem number_theory_4785_2 (x : ℕ) : 4 * x ≡ 11 [MOD 19] ↔ x ≡ 17 [MOD 19] := by
  simp [← ZMod.eq_iff_modEq_nat]
  constructor
  . intro h
    -- multiple 5 at both side of h
    apply_fun ((5 : ZMod 19) * ·) at h
    -- conclude x=17 mod 19 by simple calculation
    rwa [← mul_assoc, show 5*4=(1 : ZMod 19) from rfl, show 5*11=(17 : ZMod 19) from rfl, one_mul] at h
  -- verify the answer is correct
  . intro h
    rw [h]
    rfl
