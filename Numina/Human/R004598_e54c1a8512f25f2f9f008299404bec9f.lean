import Mathlib

/- If the discriminant of a quadratic polynomial is negative, then it has no roots. -/
lemma discrim_neg_ne_zero {a b c : ℝ} (h : a ≠ 0) (hn : discrim a b c < 0) (x : ℝ)
  : a * (x * x) + b * x + c ≠ 0 := by
    -- if the discriminant isn't a square, then there are no roots
    apply (quadratic_eq_zero_iff_discrim_eq_sq h x).mp.mt

    -- assume the discriminant is a square
    by_contra eq_sq

    -- then it's positive
    have discrim_pos : (0 : ℝ) ≤ discrim a b c := by
      rw [eq_sq]
      positivity

    -- contradiction
    linarith

/- x ^ 2 - x + 1 has no roots -/
lemma sq_sub_add_one (x : ℝ)
  : x ^ 2 - x + 1 ≠ 0 := by
    have discrim_neg : discrim (1 : ℝ) (-1) 1 < 0 := by norm_num [discrim]
    have app := discrim_neg_ne_zero (by linarith) discrim_neg x
    ring_nf at app ⊢
    tauto

/- If we have some non-zero constant c such that
  (c + 1 / x) / (c - 1 / x) = c + 1 / c
  then x is equal to 1 / c + 2 / (c ^ 2 - c + 1)
 -/
lemma Real_add_inv_div_add_inv_eq_add_div {c x : ℝ}
  (h : (c + 1 / x) / (c - 1 / x) = c + 1 / c) (ch : c ≠ 0)
  : x = 1 / c + 2 / (c ^ 2 - c + 1) := by

    -- consider x is zero
    by_cases hx : x = 0
    · subst hx

      -- then c = c * c + 1
      norm_num at h
      field_simp at h
      -- i.e. c ^ 2 - c + 1 = 0
      have eq_zero : c ^ 2 - c + 1 = 0 := by linarith
      -- but c ^ 2 - c + 1 has no roots
      have ne_zero := sq_sub_add_one c

      -- that's a contradiction
      contradiction

    -- so x is not zero

    -- consider when x is 1 / c
    by_cases hx : x = 1 / c
    · subst hx

      -- then c * c + 1 is zero
      norm_num at h
      apply_fun (· * c) at h
      field_simp at h

      -- but it's always positive
      have pos : 0 < c * c + 1 := by
        ring_nf
        positivity

      -- contradiction
      linarith

    -- so x is not 1 / c

    -- add 1 to both sides
    apply_fun (· + 1) at h

    -- simplify both sides
    convert_to 2 * c / (c - 1 / x) = (c ^ 2 + c + 1) / c at h
    · ring_nf
      field_simp
      rw [one_add_div, div_add_div_same]
      ring
      field_simp at hx
      by_contra eqq
      have x_c_eq : x * c = 1 := by linarith
      contradiction
    · ring_nf
      field_simp
      ring_nf

    -- take the reciprocal of both sides
    replace h : (c - 1 / x) / (2 * c) = c / (c ^ 2 + c + 1)
      := (div_eq_div_iff_comm _ _ _).mp h

    -- simplify LHS
    convert_to (1 / 2) - 1 / (2 * c * x) = c / (c ^ 2 + c + 1) at h
    · ring_nf
      field_simp

    -- rearrange terms
    replace h : 1 / (2 * c * x) = 1 / 2 - c / (c ^ 2 + c + 1) := by linarith

    -- turn RHS into common fraction
    convert_to 1 / (2 * c * x) = (c ^ 2 - c + 1) / (2 * (c ^ 2 + c + 1)) at h
    -- denominator is not zero
    · have : (c ^ 2 + c + 1) ≠ 0 := by
        convert_to 1 * (c * c) + 1 * c + 1 ≠ 0
        · ring
        apply discrim_neg_ne_zero
        · linarith
        · norm_num [discrim]

      field_simp
      ring


    -- take the reciprocal of both sides
    replace h : (2 * c * x) / 1 = (2 * (c ^ 2 + c + 1)) / (c ^ 2 - c + 1)
      := (div_eq_div_iff_comm _ _ _).mp h

    -- simplify
    norm_num at h

    -- extract factor of 2 on both sides
    replace h : 2 * (c * x) = 2 * ((c ^ 2 + c + 1) / (c ^ 2 - c + 1)) := by
      ring_nf at h ⊢
      linarith

    -- cancel 2
    replace h : (x * c) = ((c ^ 2 + c + 1) / (c ^ 2 - c + 1)) := by linarith

    -- isolate x in LHS
    replace h : x = ((c ^ 2 + c + 1) / (c ^ 2 - c + 1)) / c := by
      rw [←eq_div_iff] at h
      tauto
      tauto

    -- then we have our expression
    convert h using 1
    -- denominator is non-zero
    · have ne_zero : (c ^ 2 - c + 1) ≠ 0 := sq_sub_add_one c
      field_simp
      ring_nf

/- Solve the following equations:


$$

\begin{aligned}
& \frac{1.618+\frac{1}{x}}{1.618-\frac{1}{x}}=1.618+\frac{1}{1.618} \\
& \frac{0.618+\frac{1}{x}}{0.618-\frac{1}{x}}=0.618+\frac{1}{0.618}
\end{aligned}

$$


For 2nd graders, substitute the values 1.618 and 0.618 with $(\sqrt{5}+1) / 2$ and $(\sqrt{5}-1) / 2$, respectively. -/
theorem algebra_288410 {x1 x2 : ℝ}
  (h1 : ((√5 + 1) / 2 + 1 / x1) / ((√5 + 1) / 2 - 1 / x1) = ((√5 + 1) / 2) + 1 / ((√5 + 1) / 2))
  (h2 : ((√5 - 1) / 2 + 1 / x2) / ((√5 - 1) / 2 - 1 / x2) = ((√5 - 1) / 2) + 1 / ((√5 - 1) / 2))
  : x1 = (√5 + 1) / 2 ∧ x2 = √5 + 2 := by

    -- let c1 be (√5 + 1) / 2
    set c1 := (√5 + 1) / 2
    -- let c2 be (√5 - 1) / 2
    set c2 := (√5 - 1) / 2

    -- c1 is non-zero
    have c1_ne : c1 ≠ 0 := by positivity

    -- so we have that x1 = 1 / c1 + 2 / (c1 ^ 2 - c1 + 1)
    have x1_eq := Real_add_inv_div_add_inv_eq_add_div h1 c1_ne

    -- c2 is non-zero
    have c2_ne : c2 ≠ 0 := by
      norm_num [c2]
      have one_lt_sqrt : 1 < √5 := by
        rw [Real.lt_sqrt]
        norm_num
        norm_num
      linarith

    -- so x2 = 1 / c2 + 2 / (c2 ^ 2 - c2 + 1)
    have x2_eq := Real_add_inv_div_add_inv_eq_add_div h2 c2_ne

    -- we know powers of square roots of 5

    -- √5 ^ 2 = 5
    have sqrt_two : √5 ^ 2 = 5 := Real.sq_sqrt (by positivity)

    -- √5 ^ 3 = √5 * 5
    have sqrt_three : √5 ^ 3 = √5 * 5 := by
      convert_to √5 ^ (2 + 1) = √5 * 5
      rw [pow_add, sqrt_two]
      ring

    -- √5 ^ 4 = 25
    have sqrt_four : √5 ^ 4 = 25 := by
      convert_to √5 ^ (2 + 2) = 25
      rw [pow_add, sqrt_two]
      ring

    -- so we know the values of x1 and x2
    split_ands
    -- first x1
    · convert x1_eq using 1
      -- denominator is not zero
      have ne_zero := sq_sub_add_one c1

      -- simplify
      field_simp
      ring_nf

      -- simplify squares
      rw [sqrt_two, sqrt_three, sqrt_four]

      -- simplify
      ring_nf
    -- then x2
    · convert x2_eq using 1
      -- denominator is not zero
      have ne_zero := sq_sub_add_one c2

      -- simplify
      field_simp
      ring_nf

      -- simplify squares
      rw [sqrt_two, sqrt_three, sqrt_four]

      -- simplify
      ring_nf