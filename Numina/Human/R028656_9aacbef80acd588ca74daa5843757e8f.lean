import Mathlib

/- Solve the following equations:
a) $2+\frac{5}{4 x}-\frac{15}{4 x(8 x+3)}=\frac{2(7 x+1)}{7 x-3}$,
b) $\frac{2}{x}+\frac{1}{x^{2}}-\frac{7+10 x}{x^{2}\left(x^{2}+7\right)}=\frac{2}{x+\frac{3}{x+\frac{4}{x}}}$. -/
theorem algebra_260737_1 {x : ℝ} (hx : x ≠ 0) (hx' : 8*x+3 ≠ 0) (hx'': 7*x-3 ≠ 0)
  : 2 + 5 / (4 * x) - 15 / (4 * x * (8 * x + 3)) = (2 * (7 * x + 1)) / (7 * x - 3) ↔ x = 9 := by
  constructor <;> rintro h
  . -- multiply all denominators and normalize to get a cubic equation
    field_simp at h
    ring_nf at h
    replace h : 96 * x^2 * (x - 9) = 0 := by linear_combination h
    -- due to x ≠ 0, we get x = 9 = 0
    simp [hx] at h
    linarith
    -- 9 is a root, prove by pluggin in
  . rw [h]
    norm_num

theorem algebra_260737_2 {x : ℝ} (hx : x ≠ 0)
  : 2 / x + 1 / x ^ 2 - (7 + 10 * x) / (x ^ 2 * (x ^ 2 + 7)) = 2 / (x + 3 / (x + 4 / x)) ↔ x = 4 := by
  constructor <;> rintro h
    -- first normalize the rhs
  . have h' : x + 4 / x = (x^2 + 4) / x := by field_simp; ring
    rw [h'] at h
    replace h' : x + 3 / ((x ^ 2 + 4) / x) = (x^3 + 7 * x) / (x^2 + 4) := by field_simp; ring
    rw [h'] at h
    -- change one of the dnenmoinators so that field_simp can handle it better
    rw [show x^3 + 7*x = x * (x^2 + 7) by ring] at h
    -- multiply all denominator and normalize to get a 8 degree equation
    field_simp at h
    ring_nf at h
    replace h : x^5 * (x - 4) * (x ^ 2 + 7) = 0 := by linear_combination h
    -- x ≠ 0 and x^2 + 7 ≠ 0, so we get x -4 = 0
    simp [hx, show x^2 + 7 ≠ 0 by positivity] at h
    linarith
    -- 4 is a root, prove by pluggin in
  . rw [h]
    norm_num