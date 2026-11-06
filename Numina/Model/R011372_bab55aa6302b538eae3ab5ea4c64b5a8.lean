import Mathlib

theorem algebra_241580 (ax ay ab xy yb xb u v vm vb t1 t2: ℝ)
    (abpos: ab > 0) (vpos : v > 0) (upos : u > 0)
    (hxy : xy = 56 / 225 * ab) (hvm : vm = 2 * v + u) (hvb : vb = 3 * v - u) (hay : ay = ax + xy)
    (habx : ab = ax + xb) (haby : ab = ay + yb) (hayx : ay = ax + xy) (hxby : xb = xy + yb)
    (hmax : ax = vm * t1) (hmxb : xb = vb * t1) (hmxy : xy = vm * t2) (hmyb : yb = vb * t2) :
    ay = 161 / 225 * ab ∨ ay = 176 / 225 * ab := by

  have habx' : ab = ax + xb := by exact habx
  
  rw[hmax, hmxb, hvm, hvb] at habx'
  have ht1 : t1 = ab / (5 * v) := by ring_nf at habx'; field_simp; linarith
  rw[ht1, hvm] at hmax
  
  have hax : ax = (2 + (u / v)) / 5 * ab := by
    field_simp at hmax ⊢
    ring_nf at hmax ⊢
    linarith
  
  suffices u / v = 1 / 3 ∨ u / v = 2 / 3 by
    obtain h1|h2 := this
    · rw[h1] at hax
      rw[hax, hxy] at hay
      ring_nf at hay
      left
      linarith
    · rw[h2] at hax
      rw[hax, hxy] at hay
      ring_nf at hay
      right
      linarith
  
  have : vm ≠ 0 := by linarith
  
  have ht2 : t2 = xy / vm := by field_simp; linarith
  
  rw[hax, hxby, hmxy, hmyb, ht2, hvm, hvb, hxy] at habx
  have eq : ((u / v) - (1 / 3)) * ((u / v) - (2 / 3)) = 0 := by
    have hvnz : v ≠ 0 := by linarith
    have hdnz : 225 * (2 * v + u) ≠ 0 := by linarith
    field_simp at habx ⊢
    ring_nf at habx ⊢
    rw[mul_assoc (ab * v) u 1125, mul_assoc ab v (u * 1125), mul_assoc, ← mul_add] at habx
    rw[mul_assoc (ab * v) u 900, mul_assoc ab v (u * 900), mul_assoc, ← mul_add] at habx
    rw[mul_assoc, ← mul_add, mul_comm, mul_comm ab] at habx
    have hk := congrFun (congrArg HMul.hMul habx) (1/ab)
    rw[mul_assoc, ← mul_div_assoc, mul_one, div_self (by linarith)] at hk
    rw[mul_assoc, ← mul_div_assoc, mul_one, mul_one, div_self (by linarith)] at hk
    ring_nf at hk
    linarith
  
  rw[mul_eq_zero] at eq
  obtain eq1|eq2 := eq
  · left
    linarith
  · right
    linarith