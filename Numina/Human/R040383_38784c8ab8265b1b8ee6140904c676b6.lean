import Mathlib

/- Determine the smallest non-negative integer $a$ that satisfies the congruences: \begin{align*}
&a\equiv 2\pmod 3,\\
&a\equiv 4\pmod 5,\\
&a\equiv 6\pmod 7,\\
&a\equiv 8\pmod 9.
\end{align*} -/
theorem number_theory_19241 :
    IsLeast {a | 0 ≤ a ∧ a ≡ 2 [ZMOD 3] ∧ a ≡ 4 [ZMOD 5] ∧ a ≡ 6 [ZMOD 7] ∧ a ≡ 8 [ZMOD 9]} 314 := by
  refine ⟨by decide, ?_⟩
  rintro a ⟨ha0, h1, h2, h3, h4⟩
  simp_all only [Int.ModEq]
  omega