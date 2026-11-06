import Mathlib
open Real

/-
Two walls and the ceiling of a room meet at right angles at point $P.$ A fly is in the air one meter from one wall, eight meters from the other wall, and nine meters from point $P$. How many meters is the fly from the ceiling?

(A) √13 (B) √14 (C) √15 (D) 4 (E) √17
-/

theorem geometry_96037
  {a b d : ℝ}
  (ha : a = 1)
  (hb : b = 8)
  (hc : d = 9)
  : √(a^2 + b^2 + 4^2) = d
:= by
  -- Substitute in given
  rw [ha, hb, hc]
  -- Simplify
  norm_num
  -- Square both sides
  rw [(by norm_num : (81 : ℝ) = 9 * 9)]
  simp