import Mathlib

theorem number_theory_4850_1 {x : ℤ} (hx : 5 * x ≡ 3 [ZMOD 14]) :
    x ≡ 9 [ZMOD 14] := by
  rw [show (14 : ℤ ) = ↑(14 : ℕ) from rfl, ← ZMod.intCast_eq_intCast_iff] at hx
  push_cast at hx
  -- multiple 3 at both side of hx
  apply_fun (3 * ·) at hx
  -- conclude x=9 mod 14 by simple calculation
  rwa [← mul_assoc, show 3*5=(1 : ZMod 14) from rfl, one_mul, show (3 : ZMod 14)*3=↑(9 : ℤ) from rfl,
    ZMod.intCast_eq_intCast_iff, show ↑(14 : ℕ) = (14 : ℤ ) from rfl] at hx

theorem number_theory_4850_2 {x : ℤ} (hx : 4 * x ≡ 7 [ZMOD 15]) :
    x ≡ 13 [ZMOD 15] := by
  have hcast : (15 : ℤ) = ↑(15 : ℕ) := rfl
  rw [hcast, ← ZMod.intCast_eq_intCast_iff] at hx
  push_cast at hx
  -- multiple 4 at both side of hx
  apply_fun (4 * ·) at hx
  -- conclude x=13 mod 15 by simple calculation
  rwa [← mul_assoc, show 4*4=(1 : ZMod 15) from rfl, one_mul, show (4:ZMod 15)*7=↑(13 : ℤ) from rfl,
    ZMod.intCast_eq_intCast_iff, ← hcast] at hx

theorem number_theory_4850_3 {x : ℤ} (hx : 3 * x ≡ 5 [ZMOD 16]) :
    x ≡ 7 [ZMOD 16] := by
  rw [show (16 : ℤ ) = ↑(16 : ℕ) from rfl, ← ZMod.intCast_eq_intCast_iff] at hx
  push_cast at hx
  -- multiple 11 at both side of hx
  apply_fun (11 * ·) at hx
  -- conclude x=7 mod 16 by simple calculation
  rwa [← mul_assoc, show 11*3=(1 : ZMod 16) from rfl, one_mul, show (11 : ZMod 16)*5=↑(7 : ℤ) from rfl,
    ZMod.intCast_eq_intCast_iff, show ↑(16 : ℕ) = (16 : ℤ ) from rfl] at hx