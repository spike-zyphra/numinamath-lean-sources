import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

open Real

/-
Let $a$ be a natural number and $b$ and $c$ be integers such that the equation
$a x^{2} + b x + c = 0$ has two distinct solutions in the interval
$\left\langle 0, \frac{1}{2}\right]$. Prove that $a \geqslant 6$.
-/
theorem algebra_242644 (a b c : ℤ) (pos_a : 0 < a) :
  ( ∃ x y : ℝ, x ≠ y ∧
    x ∈ Set.Ioc 0 (1 / 2) ∧
    y ∈ Set.Ioc 0 (1 / 2) ∧
    a * x ^ 2 + b * x + c = 0 ∧
    a * y ^ 2 + b * y + c = 0
  ) → 6 ≤ a := by
  rintro ⟨ x, y, ne, x_range, y_range, x_quad, y_quad ⟩

  -- Get the discriminants for each quadratic
  rw [pow_two] at x_quad y_quad
  let d_x := discrim_eq_sq_of_quadratic_eq_zero x_quad
  let d_y := discrim_eq_sq_of_quadratic_eq_zero y_quad
  rw [pow_two] at d_x d_y

  -- Show positivity of d because of there being two distinct roots
  have pos_discrim : (0 : ℝ) < discrim ↑a ↑b ↑c := by
    -- Proof by contradiction, show that if d = 0, x = y which is false
    have discrim_ne_zero : discrim ↑a ↑b ↑c ≠ (0 : ℝ) := by
      by_contra
      simp_all
      -- Solve for x
      have : x = -b / (2 * a) := by
        field_simp
        linear_combination d_y
      -- Solve for y
      have : y = -b / (2 * a) := by
        field_simp
        linear_combination d_x
      simp_all
    simp_all

  have x_roots := (quadratic_eq_zero_iff (by positivity) d_x x).mp x_quad
  have y_roots := (quadratic_eq_zero_iff (by positivity) d_y y).mp y_quad
  -- Once we have the roots, we no longer need the quadratic equations
  clear x_quad y_quad
  -- Rewrite discrims as squares again
  rw [<- pow_two] at d_x d_y

  -- Take the square root of both sides
  apply congrArg sqrt at d_x
  apply congrArg sqrt at d_y
  -- Clear square root of squares with absolute values
  rw [sqrt_sq_eq_abs] at d_x d_y
  rw [<- Mathlib.Tactic.RingNF.add_neg] at x_roots y_roots

  -- Let s and t be the square roots of the discriminants
  generalize hs : 2 * a * x + b = s at *
  generalize ht : 2 * a * y + b = t at *

  -- Rewrite s and t with their absolute value at each root
  replace x_roots : x = (-b + |s|) / (2 * a) ∨ x = (-b + -|s|) / (2 * a) := by
    match abs_choice s with
    | Or.inl pos => rwa [pos]
    | Or.inr neg =>
      norm_num [neg]
      exact x_roots.symm
  replace y_roots : y = (-b + |t|) / (2 * a) ∨ y = (-b + -|t|) / (2 * a) := by
    match abs_choice t with
    | Or.inl pos => rwa [pos]
    | Or.inr neg =>
      norm_num [neg]
      exact y_roots.symm

  -- With absolute values, the cases for both roots can be rewritten in terms of just the discriminant
  simp [<- d_x, <- d_y] at x_roots y_roots
  clear d_x d_y ht hs

  -- Prove the main goal for a given assignment of x, y to the pos/neg solutions
  have xy_or_yx {x y : ℝ} :
    x ∈ Set.Ioc 0 (1 / 2) →
    y ∈ Set.Ioc 0 (1 / 2) →
    x = (-b + √(discrim a b c)) / (2 * a) ∧
    y = (-b + -√(discrim a b c)) / (2 * a) →
      6 ≤ a := by

    -- Clear irrelevant main goal hypotheses
    clear x_range y_range x_roots y_roots
    rintro x_range y_range ⟨ x_eq, y_eq ⟩

    -- Get the inequalities from the set definition
    have ⟨ x_pos, _ ⟩ := x_eq ▸ x_range
    have ⟨ y_pos, _ ⟩ := y_eq ▸ y_range

    -- We only need the inequalities now
    clear x_eq y_eq x_range y_range

    -- Let s be the square root of d
    generalize hs : √(discrim ↑a ↑b ↑c) = s at *
    -- Solve for s
    field_simp at x_pos y_pos

    -- Simplifiy upper bounds
    replace s_le : s ≤ a + b := by
      have : (2 * a) * ( (-↑b + s) / (2 * ↑a)) ≤ (2 * a) * (1/2) := by
        gcongr
      field_simp at this
      rwa [add_comm] at this

    -- We also know this from positivity of the discrim
    have s_sq_eq_d : s^2 = discrim ↑a ↑b ↑c := by
      rw [<- hs, sq_sqrt (by linarith)]

    -- s is positive because it is a square root of a positive number
    have pos_s : 0 < s := by
      simp [<- hs, sqrt_pos_of_pos pos_discrim]
    -- b is negative by transitivity of b < -s < 0
    have neg_b : b < 0 := by
      have : -s < 0 := by
        exact neg_neg_iff_pos.mpr pos_s
      exact_mod_cast lt_trans (lt_neg_of_lt_neg y_pos) this
    -- c is positive from squaring y_pos
    have pos_c : 0 < c := by
      -- square both sides
      have this : s^2 < (-b)^2 := by
        gcongr
      -- simplify s^2 to d and simplify
      field_simp [s_sq_eq_d, discrim] at this
      exact this
    -- a + b is positivty from 0 < s ≤ a + b
    have pos_ab : 0 < a + b := by
      exact_mod_cast lt_of_lt_of_le pos_s s_le

    -- After deriving inequalities for a, b, and c we no longer need s
    clear hs x_pos y_pos s_sq_eq_d s_le pos_s
    -- Narrow pos_discrim from reals to ints
    rw [discrim] at pos_discrim
    norm_cast at pos_discrim

    -- Show transitivity from 4 ≤ 4c < a
    have four_a : 4 < a := by
      -- Derive an inequality for 4c and a
      have four_c_lt_a : 4 * c < a := by
        -- Squares are less than each other if their absolute values are too
        have : b^2 < a^2 := by
          have : 0 + -b < a + b + -b := by
            gcongr
          norm_num at this
          -- if |-b| < |a|, then (-b)^2 < a^2
          rwa [sq_lt_sq, abs_of_neg neg_b, abs_of_pos pos_a]
        have : b^2 - 4 * a * c < a^2 - 4 * a * c := by
          gcongr
        -- Apply transitivity of 0 < d < a^2 - 4ac
        have : 0 < a^2 - 4 * a * c := by
          exact lt_trans pos_discrim this
        -- Simplify
        conv at this => rhs; rhs; lhs; rw [mul_comm]
        field_simp [pow_two, mul_assoc] at this
        exact this
      -- Derive an inequality for 4 and 4c
      have four_lt : 4 ≤ c * 4 := by
        simp [le_mul_iff_one_le_left]
        linarith
      rw [mul_comm] at four_c_lt_a
      exact lt_of_le_of_lt four_lt four_c_lt_a

    -- Rewrite the positivity inequality of discrim
    have ac_lt_b_sq : a * (c * 4) < b^2 := by
        field_simp at pos_discrim
        ring_nf at pos_discrim
        simp [mul_assoc] at pos_discrim
        exact pos_discrim
    -- If a > 4, than we can substitute it
    have c16_lt_b_sq : 4 * (c * 4) < b^2 :=
      mul_lt_of_mul_lt_of_nonneg_right ac_lt_b_sq four_a.le (by linarith)
    ring_nf at c16_lt_b_sq
    clear ac_lt_b_sq
    -- Cast c to a natural absolute value to make proving positivity easier
    have : c = c.natAbs := by
      simp only [Int.natCast_natAbs, abs_of_pos pos_c]
    rw [this] at c16_lt_b_sq
    rw [<- sq_abs, <- Int.natCast_natAbs] at c16_lt_b_sq
    norm_cast at c16_lt_b_sq -- normalize to naturals
    -- Show a lower bound of 16 for b^2 from 16*c and 0 < c
    have b_sq_gt_16 : 16 < b.natAbs^2 := by
      have : 0 < c.natAbs := by positivity
      exact mul_lt_of_mul_lt_of_nonneg_right c16_lt_b_sq this
        (by linarith)
    -- Simplify squares to get 4 < |b|
    have b_gt_4 : 4 < b.natAbs := by
        exact lt_of_pow_lt_pow_left' 2 b_sq_gt_16
    -- Show a > 5 from 4 < |b| and -b < a
    omega

  -- Show that either x, y = pos, neg or vice-versa
  have pm_or_mp : (
      x = (-b + √(discrim a b c)) / (2 * a) ∧
      y = (-b + -√(discrim a b c)) / (2 * a)
    ) ∨ (
      y = (-b + √(discrim a b c)) / (2 * a) ∧
      x = (-b + -√(discrim a b c)) / (2 * a)
    ) := by cases x_roots <;> cases y_roots <;> simp_all only [
      ne_eq, one_div, Set.mem_Ioc, neg_add_cancel_comm_assoc, and_self,
      or_false, or_true, not_true_eq_false, and_false
    ]

  -- Show that proving one combination suffices
  have xy := xy_or_yx x_range y_range
  have yx := xy_or_yx y_range x_range
  cases pm_or_mp <;> simp_all