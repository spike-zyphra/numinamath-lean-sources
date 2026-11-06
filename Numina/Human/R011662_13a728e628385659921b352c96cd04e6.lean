import Mathlib

/- 18 Given the hyperbola $\frac{x^{2}}{a^{2}}-\frac{y^{2}}{b^{2}}=1\left(a, b \in \mathbf{R}^{+}\right)$ with semi-focal distance $c$, and $b^{2}=a c . P$ and $Q$ are any two points on the hyperbola, $M$ is the midpoint of $P Q$, when the slopes $k_{P Q}$ and $k_{O M}$ of $P Q$ and $O M$ both exist, find the value of $k_{P Q} \cdot k_{O M}$. -/
theorem algebra_272065 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₀ : c^2 = a^2 + b^2) (h₁ : b^2 = a * c)
    (P Q M : ℝ × ℝ) (hPQ₁: P ≠ Q)
    (hP : P ∈ {(x, y) | x^2 / a^2 - y^2 / b^2 = 1})
    (hQ : Q ∈ {(x, y) | x^2 / a^2 - y^2 / b^2 = 1})
    (hM₁ : M = ((P.1 + Q.1) / 2, (P.2 + Q.2) / 2))
    (hM₂ : M.1 ≠ 0) (hPQ₂: P.1 ≠ Q.1) :
    (P.2 - Q.2) / (P.1 - Q.1) * (M.2 - 0) / (M.1 - 0) =
    (1 + Real.sqrt 5) / 2 := by

  -- first let's simplify hypotheses `hP` and `hQ`
  simp only [Set.mem_setOf_eq] at hP hQ

  -- next we will prove that `P.1 - Q.1` isn't equal to zero
  -- and also that `a` isn't equal to zero
  -- this will be useful for tactic `field_simp`
  have Px_sub_Qx_ne_zero: P.1 - Q.1 ≠ 0 := sub_ne_zero_of_ne hPQ₂
  have Ha: a ≠ 0 := by linarith

  -- and now it's time for the tactic `field_simp`
  field_simp at hP hQ ⊢

  -- we substract equations `hP` and `hQ` to prove `H`
  -- (actually we use tactic `linarith` to prove the `H`)
  have H: (P.1 ^ 2 - Q.1 ^ 2) * b^ 2 - (P.2 ^ 2 - Q.2 ^ 2) * a ^ 2 = 0 := by
    linarith
  -- some rewrites and simplifications in the hypothesis `H`
  rw [h₁] at H
  rw [show (P.1 ^ 2 - Q.1 ^ 2) * (a * c) - (P.2 ^ 2 - Q.2 ^ 2) * a ^ 2 =
           a ^ 2 * ((P.1 ^ 2 - Q.1 ^ 2) * (c / a) - (P.2 ^ 2 - Q.2 ^ 2)) by field_simp; ring] at H
  simp only [mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    Ha, false_or, sub_eq_zero] at H

  -- now we prove the value of `c / a`
  -- by getting to quadratic equation and solving it
  have value_of_c_div_a: c / a = (1 + √5) / 2 := by
    -- first replace `b ^ 2` by `a * c` in the hypothesis `h₀`
    -- and move everything to the right side of the equation (in `h₀`)
    rw [h₁, <- sub_eq_zero] at h₀
    -- rewrite right side of the equation as product of `a ^ 2`
    -- and another expression, which is in the form that's
    -- appropriate for library lemma, that solves quadratic equations
    rw [show c ^ 2 - (a ^ 2 + a * c) = a ^ 2 * (1 * ((c / a) * (c / a)) + (- 1) * (c / a) + (- 1)) by field_simp; ring] at h₀
    -- if product is zero, then at least one multiplicand is zero
    -- also, if square of a number is zero, then the number is also zero
    rw [mul_eq_zero, sq_eq_zero_iff] at h₀
    -- `a = 0` can't be true (becuase `0 < a`),
    -- so we can remove it from `h₀`
    simp only [Ha, false_or] at h₀
    -- find the value of discrimant for the quadratic equation in `h₀`
    have value_of_discriminant: discrim 1 (-1) (-1) = (√5) * √(5) := by
      simp only [discrim]
      norm_num
    -- finally we are using library lemma meant to solve quadratic equations
    rw [quadratic_eq_zero_iff (by linarith) value_of_discriminant (c / a)] at h₀
    -- some simplification
    norm_num at h₀
    -- let's look at these two options (in `h₀`)
    obtain h₀ | h₀ := h₀
    . -- this is what we need
      exact h₀
    . -- and this is false, because `c / a` is strictly positive
      -- we will solve this case by reaching contradiction
      have Hca: 0 < c / a := div_pos hc ha
      -- `h₀` and `Hca` together means that `0 < (1 - √5) / 2)`
      rw [h₀] at Hca
      -- let's get rid of this division by `2` in `Hca`
      field_simp at Hca
      -- replace `1` with `√1`
      rw [show 1 = √1 by norm_num] at Hca
      -- now we get an obvious false statement
      have H0: (5: ℝ) < 1 := (Real.sqrt_lt_sqrt_iff_of_pos (by norm_num)).mp Hca
      -- and, yes, tactic `norm_num` takes care of it
      norm_num at H0

  -- rest is easy
  -- some rewriting and simplification and goal is solved
  rw [hM₁]
  field_simp
  rw [mul_comm (P.2 - Q.2), <- sq_sub_sq, <- H, value_of_c_div_a]
  ring_nf