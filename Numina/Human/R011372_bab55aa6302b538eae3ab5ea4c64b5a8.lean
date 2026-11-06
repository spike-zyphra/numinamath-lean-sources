import Mathlib

/- 5. A motorboat departed downstream from pier A. At the same time, a boat departed upstream from pier B towards the motorboat. After some time, they met. At the moment of their meeting, a second boat departed from B and after some time met the motorboat. The distance between the points of the first and second meetings is $\frac{56}{225}$ AB. The speeds of the current, the motorboat, and the boats are constant (the speeds of the boats are the same), and the ratio of the motorboat's own speed to the boat's own speed is $2: 3$. What part of the distance $A B$ did the motorboat travel by the time it met the second boat?

Answer. $\frac{161}{225}$ or $\frac{176}{225}$. -/
theorem algebra_241580 (ax ay ab xy yb xb u v vm vb t1 t2: ℝ)
    (abpos: ab > 0) (vpos : v > 0) (upos : u > 0)
    (hxy : xy = 56 / 225 * ab) (hvm : vm = 2 * v + u) (hvb : vb = 3 * v - u) (hay : ay = ax + xy)
    (habx : ab = ax + xb) (haby : ab = ay + yb) (hayx : ay = ax + xy) (hxby : xb = xy + yb)
    (hmax : ax = vm * t1) (hmxb : xb = vb * t1) (hmxy : xy = vm * t2) (hmyb : yb = vb * t2) :
    ay = 161 / 225 * ab ∨ ay = 176 / 225 * ab := by
  have habx' : ab = ax + xb := by exact habx
  --find the time of the first meeting t1 as a function of ab u and v, substituting the lows of motions on ax and xb
  rw[hmax, hmxb, hvm, hvb] at habx'
  have ht1 : t1 = ab / (5 * v) := by ring_nf at habx'; field_simp; linarith
  rw[ht1, hvm] at hmax
  --rearrange the low of motion to find ax in terms of ab u and v
  have hax : ax = (2 + (u / v)) / 5 * ab := by
    field_simp at hmax ⊢
    ring_nf at hmax ⊢
    linarith
  --now to show the claim it suffices to show that u/v is either 1/3 or 2/3, and it could be check by simple substitution
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
      ring_nf
      exact hay
  --it is true because one can find the time of the second meeting t2 from the low of motion of the motorboat on xy
  have : vm ≠ 0 := by linarith
  --from that explicit t2
  have ht2 : t2 = xy / vm := by field_simp; linarith
  --and by substituting everything in ab = ax + xb one can rearrange to simplify ab in the equation and find a second order equation in (u /v)
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
  --this has two solutions which are 1/3 and 2/3 and this proves the claim.
  rw[mul_eq_zero] at eq
  obtain eq1|eq2 := eq
  · left
    linarith
  · right
    linarith