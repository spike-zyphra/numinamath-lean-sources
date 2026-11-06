import Mathlib

/-The lines $-2x + y = k$ and $0.5x + y = 14$ intersect when $x = -8.4$. What is the value of $k$?-/
theorem number_theory_10291 (k y: ℝ) (hp : 0.5 * (-8.4) +y = 14 ) (hq: -2 * (-8.4) +y = k ) : k = 35 := by
  --利用hp得到x=-8.4时y=18.2
  have h₁ : y=18.2:=by
    calc
    y = 0.5 * (-8.4) +y - 0.5 * (-8.4) :=by ring
    _ = 14 - 0.5 * (-8.4) :=by rw[hp]
    _ = 18.2 :=by ring
  -- 利用hq 和h₁ 计算得到k=35
  calc
  k= -2 * (-8.4) +y := by rw[hq]
  _ =-2 * (-8.4) +18.2:=by rw[h₁]
  _ = 35 := by ring
