import Mathlib

/- Problem 3. Determine all real values of $(x, y, z)$ for which

$$
\begin{array}{cccc}
x+y+z & = & 1 \\
x^{2} y+y^{2} z+z^{2} x & = & x y^{2}+y z^{2}+z x^{2} \\
x^{3}+y^{2}+z & = & y^{3}+z^{2}+x
\end{array}
$$ -/
theorem algebra_177572 :
    { (x, y, z) : ℝ × ℝ × ℝ | x + y + z = 1 ∧ x ^ 2 * y + y ^ 2 * z + z ^ 2 * x = x * y ^ 2 + y * z ^ 2 + z * x ^ 2 ∧ x ^ 3 + y ^ 2 + z = y ^ 3 + z ^ 2 + x } = { (1 / 3, 1 / 3, 1 / 3), (0, 0, 1), (0, 1, 0), (2 / 3, -1 / 3, 2 / 3), (1, 0, 0), (-1, 1, 1)} := by
  ext ⟨x, y, z⟩
  simp [-one_div]
  constructor
  -- We first verify that the given solutions are indeed solutions.
  swap
  . rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    all_goals
      norm_num
  -- If x, y, z is a solution
  intro ⟨h₁, h₂, h₃⟩
  -- We get `(x - y) * (x - z) * (y - z) = 0` from the second equation.
  replace h₂ : (x - y) * (x - z) * (y - z) = 0 := by linear_combination h₂
  simp [sub_eq_zero] at h₂
  -- So `x = y` or `x = z` or `y = z`.
  rcases h₂ with (rfl | rfl) | rfl
  . -- If `x = y`, we get `(x - z) * (x + z - 1) = 0` from the third equation.
    replace h₃ : (x - z) * (x + z - 1) = 0 := by linear_combination h₃
    simp [sub_eq_zero] at h₃
    -- So `x = z` or `x + z = 1`.
    -- Then we solve the linear system of equations with `linarith`.
    rcases h₃ with rfl | h₃
    . left
      simp
      linarith
    . right; left
      simp
      constructor <;> linarith
  . -- If `x = z`, we get `(x - y) * (x ^ 2 + y ^ 2 + x * y - x - y) = 0` from the third equation.
    replace h₃ : (x - y) * (x ^ 2 + y ^ 2 + x * y - x - y) = 0 := by linear_combination h₃
    simp [sub_eq_zero] at h₃
    -- So `x = y` or `x ^ 2 + y ^ 2 + x * y - x - y = 0`.
    rcases h₃ with rfl | h₃
    . left
      simp
      linarith
    . -- We solve the quadratic equation with `nlinarith` and get `x = 0` or `x = 2 / 3`.
      replace h₂ : x * (x - 2 / 3) = 0 := by nlinarith
      simp [sub_eq_zero] at h₂
      -- The rest is trivial.
      rcases h₂ with rfl | rfl
      . right; right; left
        simp
        linarith
      . right; right; right; left
        simp
        linarith
  . -- If `y = z`, we get `(x - y) * (x ^ 2 + x * y + y ^ 2 - 1) = 0` from the third equation.
    replace h₃ : (x - y) * (x ^ 2 + x * y + y ^ 2 - 1) = 0 := by linear_combination h₃
    simp [sub_eq_zero] at h₃
    -- So `x = y` or `x ^ 2 + x * y + y ^ 2 - 1 = 0`.
    rcases h₃ with rfl | h₃
    . left
      simp
      linarith
    . -- We solve the quadratic equation with `nlinarith` and get `y = 0` or `y = 1`.
      replace h₂ : y * (y - 1) = 0 := by nlinarith
      simp [sub_eq_zero] at h₂
      -- The rest is trivial.
      rcases h₂ with rfl | rfl
      . right; right; right; right; left
        simp
        linarith
      . right; right; right; right; right
        simp
        linarith
