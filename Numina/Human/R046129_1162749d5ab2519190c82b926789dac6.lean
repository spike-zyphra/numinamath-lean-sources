import Mathlib

/-If $x \equiv 4 \pmod{19}$ and $y \equiv 7 \pmod{19}$, then find the remainder when $(x + 1)^2 (y + 5)^3$ is divided by 19.-/
theorem number_theory_23481 (x y : ℤ) (hx : x ≡ 4 [ZMOD 19]) (hy : y ≡ 7 [ZMOD 19]) :
    ((x + 1)^2 * (y + 5)^3) ≡ 13 [ZMOD 19] := by
  -- If $x \equiv 4 \pmod{19}$ and $y \equiv 7 \pmod{19}$, then \begin{align*}
  -- (x + 1)^2 (y + 5)^3 &\equiv 5^2 \cdot 12^3 \\
  -- &\equiv 25 \cdot 1728 \\
  -- &\equiv 6 \cdot 18 \\
  -- &\equiv 108 \\
  -- &\equiv \boxed{13} \pmod{19}.
  -- \end{align*}
  have emod₁: (x + 1)^2 ≡ 5^2 [ZMOD 19] := by
    rw [Int.ModEq]
    rw [Int.ModEq] at hx
    simp
    rw [pow_two, Int.mul_emod]
    have : (x + 1) % 19 = 5 := by omega
    rw [this]
    omega
  have emod₂: (y + 5)^3 ≡ 12^3 [ZMOD 19] := by
    rw [Int.ModEq]
    rw [Int.ModEq] at hy
    simp
    rw [pow_three, Int.mul_emod, Int.mul_emod (y + 5)]
    have : (y + 5) % 19 = 12 := by omega
    rw [this]
    simp
  rw [Int.ModEq] at emod₁ emod₂
  rw [Int.ModEq, Int.mul_emod, emod₁, emod₂]
  simp
