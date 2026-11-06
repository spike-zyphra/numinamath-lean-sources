import Mathlib

/-If the parabola $y_1 = x^2 + 2x + 7$ and the line $y_2 = 6x + b$ intersect at only one point, what is the value of $b$?-/
theorem algebra_18525 (b : ℝ) (h : ∃! x, x ^ 2 + 2 * x + 7 = 6 * x + b) :
    b = 3 := by
  -- If the curves $y_1$ and $y_2$ intersect at only one point, then there should be only one solution to the equation $x^2 + 2x + 7 = 6x + b$. To find $b$, we first rearrange the equation to get $x^2 -4x + (7-b) = 0$. This equation has only one solution if and only if the discriminant of $x^2 - 4x + (7 - b) = 0$. Thus, we need  \begin{align*}
  -- 16 - 4(7-b) &= 0 \quad \Rightarrow \\
  -- 4b &= 12 \quad \Rightarrow \\
  -- b &= \boxed{3}.
  -- \end{align*}

  have my_lemma {a b c : ℝ} (ha : a ≠ 0) : (∃! x, a * x^2 + b * x + c = 0) ↔ discrim a b c = 0 := by
    constructor
    . intro hx
      obtain ⟨x, hx, h⟩ := hx
      simp at h
      rw [pow_two] at hx
      have : ∃s, discrim a b c = s^2 := by
        by_contra!
        have := quadratic_ne_zero_of_discrim_ne_sq this x
        absurd this
        exact hx
      rcases this with ⟨s, hs⟩
      have exist_s : ∃ s, discrim a b c = s * s := by use s; rw [hs, pow_two]
      have : (-b + s) / (2 * a) = (-b - s) / (2 * a) := by
        by_contra! p
        have : a * ((-b + s) / (2 * a)) ^ 2 + b * ((-b + s) / (2 * a)) + c = 0 := by
          rw [pow_two, ←mul_assoc]
          rw [pow_two] at hs
          convert (quadratic_eq_zero_iff ha hs ((-b + s) / (2 * a))).mpr
          simp
          ring_nf
        have eq₁ := h ((-b + s) / (2 * a)) this
        have : a * ((-b - s) / (2 * a)) ^ 2 + b * ((-b - s) / (2 * a)) + c = 0 := by
          rw [pow_two, ←mul_assoc]
          rw [pow_two] at hs
          convert (quadratic_eq_zero_iff ha hs (((-b - s) / (2 * a)))).mpr
          simp
          ring_nf
        have eq₂ := h ((-b - s) / (2 * a)) this
        rw [eq₁, eq₂] at p
        absurd p
        linarith
      rw [hs]
      simp
      rw [div_left_inj'] at this
      linarith
      simp
      exact ha

    . intro h
      use -b/(2 * a)
      have := quadratic_eq_zero_iff_of_discrim_eq_zero ha h
      constructor
      . replace this := this (-b / (2 * a))
        ring_nf at *
        aesop
      . intro y hy
        rw [pow_two, ←mul_assoc] at hy
        specialize this y
        apply this.mp
        rw [← mul_assoc, hy]

  have : discrim 1 (-4) (7 - b) = 0 := by
    apply (my_lemma (by norm_num)).mp
    rcases h with ⟨x, hx, h⟩
    use x
    simp
    use (by linarith)
    simp at h
    intro y hy
    specialize h y (by linarith)
    exact h

  unfold discrim at this
  linarith
