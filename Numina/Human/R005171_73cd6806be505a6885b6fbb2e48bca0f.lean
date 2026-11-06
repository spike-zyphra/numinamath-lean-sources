import Mathlib

open Real

-- Solve over the positive real numbers the functional equation  $$ f(x y+f(x))=x f(y)+2 $$
theorem algebra_606011 (f : ℝ → ℝ) (over_pos : ∀ x > 0, f x > 0) :
    (∀ x > 0, ∀ y > 0, f (x * y + f x) = x * f y + 2) ↔ ∀ x > 0, f x = x + 1 := by
  constructor
  . intro p
    have case_gt_1 : ∀ x > 1, f x = x + 1 := by
      have f_1_pos := over_pos 1 (by simp)
      have f_x_eq_linear : ∀ x > 1, f x = (2 / f 1) * x + (f 1 - 2 / f 1) := by
        intro x' x'_pos
        let x := f 1 / (x' - 1)
        have x'_eq : x' = 1 + f 1 / x := by
          unfold x
          field_simp
        have x_pos : 0 < x := by
          unfold x
          field_simp [x'_pos]
        -- Make the following substitutions to the equation:
        -- 1. $(x, 1) \rightarrow f(x + f(x)) = xf(1) + 2$
        have f_x_add_f_x_eq := p x x_pos 1 (by simp)
        simp at f_x_add_f_x_eq
        -- 2. $(1, x + f(x)) \rightarrow f(x + f(x) + f(1)) = f(x + f(x)) + 2 = xf(1) + 4$
        have := over_pos x x_pos
        have := p 1 (by simp) (x + f x) (by linarith)
        rw [show 1 * (x + f x) + f 1 = x + f x + f 1 by ring] at this
        simp at this
        rw [f_x_add_f_x_eq] at this
        rw [show x * f 1 + 2 + 2 = x * f 1 + 4 by ring] at this
        -- 3. $(x, 1 + \frac{f(1)}{x}) \rightarrow f(x + f(x) + f(1)) = xf\biggl(1 + \frac{f(1)}{x}\biggr) + 2$
        have : f 1 / x > 0 := by
          exact div_pos f_1_pos x_pos
        have := p x x_pos (1 + f 1 / x) (by linarith)
        rw [
          show x * (1 + f 1 / x) + f x = x + f x + f 1 by
            field_simp
            ring
          ] at this
        -- It then follows from (2) and (3) that $f(1 + \frac{f(1)}{x}) = f(1) + \frac{2}{x}$, so we know that this function is linear for $x > 1$.
        have : x * f 1 + 4 = x * f (1 + f 1 / x) + 2 := by
          linarith
        have : f (1 + f 1 / x) = f 1 + 2 / x := by
          set x'' := 1 + f 1 / x
          field_simp
          unfold x'' at *
          clear x''
          linarith
        show f x' = (2 / f 1) * x' + (f 1 - 2 / f 1)
        . rw [x'_eq]
          convert this using 1
          field_simp
          ring
      -- Substitute $f(x) = ax+b$ and solve for $a$ and $b$ in the functional equation; we find that $f(x) = x + 1 \forall x > 1$.
      have f_1_eq_2 : f 1 = 2 := by
        have := p 2 (by simp) 2 (by simp)
        have eq : f (2 * 2 + f 2) - (2 * f 2 + 2) = 0 := by
          linarith
        norm_num at eq
        have f_2_pos := over_pos 2 (by simp)
        rw [f_x_eq_linear (4 + f 2) (by linarith)] at eq
        rw [f_x_eq_linear 2 (by simp)] at eq
        ring_nf at eq
        field_simp at eq
        ring_nf at eq
        have : f 1 ^ 4 - 2 * f 1 ^ 2 - 4 * f 1 = 0 := by
          linarith
        have : f 1 ^ 3 - 2 * f 1 - 4 = 0 := by
          nlinarith
        have mul_eq_0 : (f 1 - 2) * (f 1 ^ 2 + 2 * f 1 + 2) = 0 := by
          linarith
        have : f 1 ^ 2 + 2 * f 1 + 2 ≠ 0 := by
          nlinarith
        simp [this] at mul_eq_0
        linarith
      norm_num [f_1_eq_2] at f_x_eq_linear
      exact f_x_eq_linear
    -- Now, we can let $x > 1$ and $y \le 1$. Since $f(x) = x + 1$, $xy + f(x) > x > 1$, so $f(xy + f(x)) = xy + x + 2 = xf(y) + 2$. It becomes clear then that $f(y) = y + 1$ as well, so $f(x) = x + 1$ is the only solution to the functional equation.
    have case_le_1 : ∀ y, y > 0 ∧ y ≤ 1 → f y = y + 1 := by
      rintro y ⟨y_pos, y_le_1⟩
      let x : ℝ := 2
      have p_x_y := p x (by simp) y y_pos
      have : x * y + f x > 1 := by
        rw [case_gt_1 x (by simp)]
        unfold x
        linarith
      rw [case_gt_1 _ this] at p_x_y
      rw [case_gt_1 x (by simp)] at p_x_y
      ring_nf at p_x_y
      linarith
    intro x x_pos
    by_cases w_x_gt_1 : x > 1
    . exact case_gt_1 x w_x_gt_1
    . exact case_le_1 x (by
        constructor
        . exact x_pos
        . linarith
      )
    -- ~jkmmm3
  . intro f_x_eq x x_pos y y_pos
    rw [f_x_eq x x_pos, f_x_eq y y_pos]
    have : x * y + (x + 1) > 0 := by
      nlinarith
    rw [f_x_eq _ this]
    ring
