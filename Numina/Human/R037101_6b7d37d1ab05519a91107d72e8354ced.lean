import Mathlib

/- 7. Prove that the system of equations has no solutions:


$$

\left\{\begin{array}{c}
x^{3}+x+y+1=0 \\
y x^{2}+x+y=0 \\
y^{2}+y-x^{2}+1=0
\end{array}\right.

$$
 -/
theorem algebra_235978 (x y : ℝ) :
    x^3 + x + y + 1 ≠ 0 ∨ y * x^2 + x + y ≠ 0 ∨ y^2 + y - x^2 + 1 ≠ 0 := by
    -- let's first obtain the system from the formalization
    by_contra h
    push_neg at h
    obtain ⟨hx, hy, hz⟩ := h
    -- then we notice that 0 = y * (first eqn.) - x * (second eqn)
    have h2:=
      calc 0
      _ = y * (x^3 + x + y + 1) - x * (y * x^2 + x + y) := by rw [hx, hy]; simp
      _ = y^2+y-x^2 := by ring_nf
    -- this gives obvious contradiction with the third equation
    linarith