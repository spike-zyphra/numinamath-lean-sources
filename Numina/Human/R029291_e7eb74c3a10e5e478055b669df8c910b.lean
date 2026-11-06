import Mathlib

/- $$
\begin{array}{l}
\text { 1. If } \frac{x}{x+1}+\frac{2 x}{(x+1)(2 x+1)}+ \\
\frac{3 x}{(x+1)(2 x+1)(3 x+1)}>1,
\end{array}
$$

then the range of real number $x$ is -/
theorem inequalities_319945 (x : ℝ) (h1: x+1 ≠ 0) (h2: 2*x+1 ≠ 0) (h3: 3*x+1 ≠ 0) :
    (x / (x + 1) + 2 * x / ((x + 1) * (2 * x + 1)) + 3 * x / ((x + 1) * (2 * x + 1) * (3 * x + 1))) > 1 ↔
    x < -1 ∨ (-1 / 2 < x ∧ x < -1 / 3) := by

    -- simplify
    have h4: (x / (x + 1) + 2 * x / ((x + 1) * (2 * x + 1)) +
      3 * x / ((x + 1) * (2 * x + 1) * (3 * x + 1)) ) - 1 =
      -1 / ((x+1) * (2*x+1) * (3*x+1)) := by
      field_simp [h1, h2, h3]
      ring

    -- ... > 1, equivalent to ... - 1 > 0
    have h5: (x / (x + 1) + 2 * x / ((x + 1) * (2 * x + 1)) +
      3 * x / ((x + 1) * (2 * x + 1) * (3 * x + 1))) > 1  ↔
      ((x+1) * (2*x+1) * (3*x+1)) < 0 := by
      rw [gt_iff_lt, ← sub_pos, h4, div_pos_iff]
      norm_num

    -- solve (x+1)(2x+1)(3x+1) < 0
    rw [h5, mul_assoc]
    constructor
    · rw [mul_neg_iff]
      rintro (hh | hh)
      · right; rw [mul_neg_iff] at hh
        rcases hh.right with hh1 | hh2
        · constructor <;> linarith only [hh1]
        · linarith only [hh.left, hh2]
      · left; linarith only [hh.left]
    · rintro (hx1 | hx2)
      · apply mul_neg_of_neg_of_pos ?_ ?_
        · linarith only [hx1]
        · apply mul_pos_of_neg_of_neg ?_ ?_
          <;> linarith only [hx1]
      · apply mul_neg_of_pos_of_neg ?_ ?_
        · linarith only [hx2]
        · apply mul_neg_of_pos_of_neg ?_ ?_
          <;> linarith only [hx2]