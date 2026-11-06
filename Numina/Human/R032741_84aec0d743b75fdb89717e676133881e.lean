import Mathlib

/- Find the real roots of
\[\frac{( x+ 1)(x - 3)}{5(x + 2)(x - 4)} + \frac{(x + 3)(x - 5)}{9(x + 4)(x - 6)} - \frac{2(x + 5)(x - 7)}{13(x + 6)(x - 8)} = \frac{92}{585}.\]Enter the real roots, separated by commas. -/
theorem algebra_22300 {x : ℝ} (hx : x ≠ -2 ∧ x ≠ 4 ∧ x ≠ -4 ∧ x ≠ 6 ∧ x ≠ -6 ∧ x ≠ 8) :
    ((x + 1) * (x - 3)) / (5 * (x + 2) * (x - 4)) +
    ((x + 3) * (x - 5)) / (9 * (x + 4) * (x - 6)) -
    2 * ((x + 5) * (x - 7)) / (13 * (x + 6) * (x - 8)) = 92 / 585 ↔
    x = 1 + Real.sqrt 19 ∨ x = 1 - Real.sqrt 19 := by
  -- notice that these polynomials all have the form of x^2-2x+C. so we can use this feature to simplify.
  let y := x^2-2*x-48
  have y_def: y = x^2-2*x-48 := rfl
  have addnz{a b : ℝ}: a ≠ -b → a+b ≠ 0 := by
    intro h
    by_contra! hc
    rw [← add_zero (-b), ← hc] at h
    simp at h
  have y40nz: y+40 ≠ 0 := by
    have: y+40 = (x+2)*(x-4) := by
      rw [y_def]; ring
    rw [this]
    apply mul_ne_zero
    · apply addnz hx.left
    · apply sub_ne_zero_of_ne hx.right.left
  have y24nz: y+24 ≠ 0 := by
    have: y+24 = (x+4)*(x-6) := by
      rw [y_def]; ring
    rw [this]
    apply mul_ne_zero
    · apply addnz hx.right.right.left
    · apply sub_ne_zero_of_ne hx.right.right.right.left
  have ynz: y ≠ 0 := by
    have hh1: (x+6)*(x-8) = y := by
      rw [y_def]; ring
    rw [← hh1]
    apply mul_ne_zero
    · apply addnz hx.right.right.right.right.left
    · apply sub_ne_zero_of_ne hx.right.right.right.right.right
  -- first term = (5+(y+40))/5(y+40) = (1/5+1/(y+40))
  have h1: ((x + 1) * (x - 3)) / (5 * (x + 2) * (x - 4)) =
    1/5 + 1/(y+40) := by
    have hh1: (x+1)*(x-3) = y+40+5 := by
      rw [y_def]; ring
    have hh2: 5*(x+2)*(x-4) = 5*(y+40) := by
      rw [y_def]; ring
    rw [hh1, hh2]
    field_simp [y40nz]
  -- second term = (9+(y+24))/9(y+24)
  have h2: ((x + 3) * (x - 5)) / (9 * (x + 4) * (x - 6)) =
    1/9 + 1/(y+24) := by
    have hh1: (x+4)*(x-6) = y+24 := by
      rw [y_def]; ring
    have hh2: 9*(x+4)*(x-6) = 9*(y+24) := by
      rw [← hh1]; ring
    have hh3: (x+3)*(x-5) = (y+24)+9 := by
      rw [y_def]; ring
    rw [hh2, hh3]
    field_simp [y24nz]
  -- third term = 2 (y+13) / 13y
  have h3: 2 * ((x + 5) * (x - 7)) / (13 * (x + 6) * (x - 8)) =
    2/13 + 2/y := by
    have hh1: (x+6)*(x-8) = y := by
      rw [y_def]; ring
    have hh2: 13 * (x + 6) * (x - 8) = 13*y := by
      rw [← hh1]; ring
    have hh3: 2 * ((x + 5) * (x - 7)) = 2*(y+13) := by
      rw [y_def]; ring
    rw [hh2, hh3]
    field_simp [ynz]
    ring
  -- substitute back, and the equation simplifies to
  -- 1/(y+40) + 1/(y+24) - 2/y + 92/585
  have h4: ((x + 1) * (x - 3)) / (5 * (x + 2) * (x - 4)) +
    ((x + 3) * (x - 5)) / (9 * (x + 4) * (x - 6)) -
    2 * ((x + 5) * (x - 7)) / (13 * (x + 6) * (x - 8)) =
      1/(y+40) + 1/(y+24) - 2/y + 92/585 := by
    rw [h1, h2, h3]
    ring
  -- now we can solve y, and then determine x.
  constructor <;> intro h
  · have eq1: 1/(y+40) + 1/(y+24) - 2/y = 0 := by
      rw [h4] at h
      linarith [h]
    -- for eq1, multiply (y+24) (y+40) y
    have eq2: 64*y+1920 = 0 := by
      have hh1: -(64*y+1920) = 0 := by
        field_simp [y40nz, y24nz, ynz] at eq1
        rw [← eq1]
        ring
      have hh2: 0 = -(0:ℝ) := by simp
      rw [hh2, ← hh1]; simp
    -- so we solve y = -30
    have eq3: y = -30 := by
      linarith [eq2]
    -- therefore x^2-2x-18 = 0
    have eq4: x^2-2*x-18 = 0 := by
      rw [y_def] at eq3
      linarith [eq3]
    -- thus we solve x
    rw [← one_mul (x^2), pow_two] at eq4
    -- following eq5 form match old version of quadratic_eq_zero_iff. in teh new version, it should be 1*(x*x)+...
    have eq5: 1*x*x + (-2)*x + (-18) = 0 := by
      rw [← eq4]; ring
    have hh1: (1:ℝ) ≠ 0 := by simp
    have hh2: discrim 1 (-2) (-18) = (2*√19)*(2*√19) := by
      rw [discrim]; ring_nf; field_simp; ring
    rw [mul_assoc, quadratic_eq_zero_iff hh1 hh2 x] at eq5
    rcases eq5 with hl | hr
    · left; rw [hl]; simp; field_simp; ring
    · right; rw [hr]; simp; field_simp; ring
  -- to verify solutions of x, we solve y and subsitute y into the expression.
  · rw [h4]
    have yeq: y = -30 := by
      rw [y_def]
      rcases h with hh | hh
      <;> rw [hh] <;> ring_nf <;> field_simp <;> ring
    rw [yeq]; ring
