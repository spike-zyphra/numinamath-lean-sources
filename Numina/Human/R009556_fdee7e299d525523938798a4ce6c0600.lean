import Mathlib

/- If $3x+7\equiv 2\pmod{16}$, then $2x+11$ is congruent $\pmod{16}$ to what integer between $0$ and $15$, inclusive? -/
theorem number_theory_16681 (x : ℤ) (h : 3 * x + 7 ≡ 2 [ZMOD 16]) :
    2 * x + 11 ≡ 13 [ZMOD 16] := by
  simp_all [Int.ModEq]
  omega