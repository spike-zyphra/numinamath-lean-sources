import Mathlib

/- Let's prove that the following system of equations has no solution in the real numbers:

\begin{gathered}
x^{3}+y^{2}=2, \\
x^{2}+x y+y^{2}-y=0 .
\end{gathered}

$$
 -/
theorem algebra_172407 (x y : ℝ) :
    x^3 + y^2 ≠ 2 ∨ x^2 + x * y + y^2 - y ≠ 0 := by
  by_contra h; simp at h
  obtain ⟨h1, h2⟩ := h
  -- prove a lemma that (x-a) * (x-b) ≤ 0 implies a ≤ x ≤ b
  have aux {x a b : ℝ} (h : a ≤ b) : (x - a) * (x - b) ≤ 0 ↔ a ≤ x ∧ x ≤ b := by
    rw [mul_nonpos_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos, or_iff_left_iff_imp]
    exact fun ⟨hxa, hbx⟩ ↦ ⟨Preorder.le_trans a b x h hbx, Preorder.le_trans x a b hxa h⟩
  -- now treating h2 as quadratic of y and using determinant as square, prove (y-0) * (y-1/4) ≤ 0 hence 0 ≤ y ≤ 4 / 3
  have y_bounds : 0 ≤ y ∧ y ≤ 4 / 3 := by
    have h := discrim_eq_sq_of_quadratic_eq_zero (show 1 * (x * x) + y * x + (y ^ 2 - y) = 0 by linear_combination h2)
    replace h : 0 ≤ discrim 1 y (y ^ 2 - y) := by rw[h]; positivity
    simp [discrim] at h
    replace h : (y - 0) * (y - 4 / 3) ≤ 0 := by linarith
    exact aux (by norm_num) |>.mp h
  -- now treating h2 as quadratic of x and using determinant as square, prove (x--1) * (y-1/3) ≤ 0 hence -1 ≤ x ≤ 1 / 3
  have x_bounds : -1 ≤ x ∧ x ≤ 1 / 3 := by
    have h := discrim_eq_sq_of_quadratic_eq_zero (show 1 * (y * y) + (x - 1) * y + x ^ 2 = 0 by linear_combination h2)
    replace h : 0 ≤ discrim 1 (x - 1) (x ^ 2) := by rw[h]; positivity
    simp [discrim] at h
    replace h : (x - -1) * (x - 1 / 3) ≤ 0 := by linarith
    exact aux (by norm_num) |>.mp h
  -- so bound y^2
  have y_ub : y ^ 2 ≤ (4 / 3) ^ 2 := by
    gcongr
    . exact y_bounds.left
    . exact y_bounds.right
  -- so bound x^3
  have x_ub : x ^ 3 ≤ (1 / 3) ^ 3 := by
    apply (Odd.strictMono_pow (by decide)).monotone
    exact x_bounds.right
  -- the bounds together prove x^3 + y^2 is too low to satisfy h1
  linarith only [h1, x_ub, y_ub]