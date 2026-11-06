import Mathlib

/-Find all real positive solutions (if any) to

$$
\begin{gathered}
x^{3}+y^{3}+z^{3}=x+y+z, \text { and } \\
x^{2}+y^{2}+z^{2}=x y z .
\end{gathered}
$$-/
theorem algebra_604906 : ¬ ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
x ^ 3 + y ^ 3 + z ^ 3 = x + y + z ∧ x ^ 2 + y ^ 2 + z ^ 2 = x * y * z := by
-- Assume the contrary that there exists such positive real numbers $x$, $y$ and $z$
  rintro ⟨x, y, z, ⟨xpos, ypos, zpos, heq1, heq2⟩⟩
-- Assume w. l. o. g. that $x$ is less or equal to $y$
  wlog xley : x ≤ y
  · specialize this y x z ypos xpos zpos; ring_nf at heq1 heq2 this
    specialize this heq1 heq2 (show _ by linarith); exact this
-- Assume w. l. o. g. that $x$ is less or equal to $z$
  wlog xlez : x ≤ z
  · specialize this z y x zpos ypos xpos; ring_nf at heq1 heq2 this
    specialize this heq1 heq2 (show _ by linarith) (show _ by linarith); exact this
-- Prove that $x$ is less or equal to $1$ by assuming the contrary and prove $x+y+z$ is less than $x^3+y^3+z^3$
  have xle1 : x ≤ 1 := by
    by_contra!; suffices : x + y + z < x ^ 3 + y ^ 3 + z ^ 3; linarith
    apply add_lt_add; apply add_lt_add; any_goals apply lt_self_pow₀; any_goals linarith
-- Prove that $x*y*z$ is less than $x^2+y^2+z^2$, which is a contradiction
  suffices : x * y * z < x ^ 2 + y ^ 2 + z ^ 2; linarith; calc
    _ ≤ y * z := by rw [mul_assoc, mul_le_iff_le_one_left]; exact xle1; positivity
    _ < 2 * y * z := by rw [mul_assoc, lt_mul_iff_one_lt_left]; simp; positivity
    _ ≤ y ^ 2 + z ^ 2 := by apply two_mul_le_add_pow_two
    _ ≤ _ := by simp [add_assoc]; exact sq_nonneg x