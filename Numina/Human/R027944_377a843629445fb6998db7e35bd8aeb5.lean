import Mathlib
open Real

/- The vertex of the parabola y = x² - 8 + c will be a point on the x-axis if the value of c is:
A:-16 B:-4 C:4 D:8 E:16 -/
theorem algebra_94587
  (c : ℝ)
  (h : ∃ k, k^2 - 8 * k + c = 0 ∧ (∀ x, k^2 - 8 * k + c ≤ x^2 - 8 * x + c)) :
  c = 16 :=
by
  obtain ⟨k, hk, hm⟩ := h
-- simplify the inequality to make it easy to discuss the value of vertex's x-coordinate
  have h1:∀t, t ^ 2 - 8 * t + c=(t-4)^2-16+c:=by intros;linarith
  have hm':∀x, (k-4)^2≤(x-4)^2:=by
    intro u;
    rw [← sub_le_sub_iff_right 16,← add_le_add_iff_right c,← h1,← h1]
    exact hm u
-- obtain the value of vertex's x-coordinate by proving k>=0 and k<=0
  have h1: 0 ≤ (k-4)^2 := sq_nonneg (k-4)
  have h2 := hm' 4
-- substituting the vertex's x-coordinate into the equation to get c
  linarith