import Mathlib
/- Compute all ordered triples $(x, y, z)$ of real numbers satisfying the following system of equations:

$$
\begin{array}{r}
x y+z=40 \\
x z+y=51 \\
x+y+z=19 .
\end{array}
$$ -/
theorem algebra_610632 : {(x, y, z) : ℝ × ℝ × ℝ | x * y + z = 40 ∧ x * z + y = 51 ∧ x + y + z = 19} = {(12, 3, 4), (6, 5.4, 7.6)}:= by
  -- Extend to work with a triple of real numbers
  ext ⟨x, y, z⟩
  constructor
  -- Forward direction: prove that any solution must be one of the two given points
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2, h3⟩
    -- Express x in terms of y and z using the third equation
    replace h3 : x = 19 - (y + z):= by linarith
    subst x
    -- Key step: shows that y + z must be either 7 or 13
    have h3 : (y + z - 7) * (y + z - 13) = 0:= by linarith
    simp at h3
    rcases h3 with h3 | h3
    -- First case: when y + z = 7
    .
      replace h3 : y + z = 7:= by linarith
      rw [h3] at h1 h2
      replace h1 : y = 3:= by linarith
      replace h2 : z = 4:= by linarith
      subst y z
      simp
      norm_num
    -- Second case: when y + z = 13
    .
      replace h3 : y + z = 13:= by linarith
      rw [h3] at h1 h2
      replace h1 : y = 27 / 5:= by linarith
      replace h2 : z = 38 / 5:= by linarith
      subst y z
      simp
      norm_num
  -- Reverse direction: prove that both given points satisfy the system
  .
    intro h
    simp
    simp at h
    rcases h with h | h
    all_goals
      rcases h with ⟨h1, h2, h3⟩
      subst x y z
      norm_num
