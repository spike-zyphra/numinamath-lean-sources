import Mathlib

/- Let $f: \mathbb{R} \rightarrow \mathbb{R}$ be a function such that
(i) For all $x, y \in \mathbb{R}$,

$$
f(x)+f(y)+1 \geq f(x+y) \geq f(x)+f(y)
$$

(ii) For all $x \in[0,1), f(0) \geq f(x)$,
(iii) $-f(-1)=f(1)=1$.

Find all such functions $f$.
Answer: $f(x)=\lfloor x\rfloor$, the largest integer that does not exceed $x$, is the only function. -/
theorem algebra_604557: {f : ℝ → ℝ |
  (∀ x y, f x + f y + 1 ≥ f (x + y) ∧ f (x + y) ≥ f x + f y) ∧
  (∀ x ∈ Set.Ico 0 1, f 0 ≥ f x) ∧
  -f (-1) = 1 ∧ f 1 = 1} = {fun x => (⌊x⌋ : ℝ)} := by
  apply Set.eq_of_subset_of_subset
  all_goals simp
  -- We will first prove that the condition implies \( f(x) = \lfloor x \rfloor \).
  . intro f h1 h2 h3 h4
    replace h3: f (-1) = -1 := by nth_rw 2 [<-h3]; simp only [neg_neg]
    ext x'
    -- Decompose \( x' \) into its integer part and fractional part.
    rw [<-Int.floor_add_fract x']
    -- First, prove \( f(x + 1) = f(x) + 1 \) by substituting two special values.
    have f_add_one (x: ℝ): f (x + 1) = f x + 1 := by
      have h' := (h1 x 1).2
      rw [h4] at h'
      have h'' := (h1 (x + 1) (-1)).2
      simp [h3] at h''
      exact le_antisymm h'' h'
    -- prove that $f(0) = 0$
    have f_zero: f 0 = 0 := by
      have h' := f_add_one 0
      simp [h4] at h'
      exact h'
    -- Prove \( f(x + n) = f(x) + n \) by induction using the two theorems above
    have f_add_int (x: ℝ) (n: ℤ): f (x + n) = f x + n := by
      induction n using Int.induction_on with
      | hz => simp
      | hp i hi =>
        simp
        norm_cast at hi
        rw [<-add_assoc, <-add_assoc, <-hi]
        exact f_add_one (x + i)
      | hn i hi =>
        simp
        rw [Int.cast_neg] at hi
        simp at hi
        rw [show x + (-i - 1) = x - i - 1 by ring_nf]
        rw [show f x + (-i - 1) = f x + -i - 1 by ring_nf]
        rw [<-hi]
        have h' := f_add_one (x - i - 1)
        simp at h'
        rw [<-sub_eq_add_neg, h']
        ring_nf
    rw [add_comm, f_add_int]
    rw [Int.fract_add_floor, add_left_eq_self]

    -- Prove that the fractional part is always equal to 0.
    have f_zero_to_one (x: ℝ) (h: x ∈ Set.Ico 0 1): f x = 0 := by
      have h' := h1 x (1 - x)
      simp [h4] at h'
      replace h' := h'.1
      simp at h
      have x_max := h.2
      -- Discuss separately based on whether \( x \) is 0.
      match lt_or_eq_of_le h.1 with
      | Or.inl x_min =>
        -- At this point, it is observed that both \( f(x) \) and \( f(1 - x) \) are less than or equal to 0
        -- their sum is less than or equal to 0, thus both \( f(x) \) and \( f(1 - x) \) must be 0.
        have h_1_sub_x_min: 0 < 1 - x := sub_pos.2 x_max
        have h_1_sub_x_max: 1 - x < 1 := sub_lt_self 1 x_min
        have f_x_nonneg := h2 x (le_of_lt x_min) x_max
        have f_1_sub_x_nonpos := h2 (1 - x) (le_of_lt h_1_sub_x_min) h_1_sub_x_max
        rw [f_zero] at f_x_nonneg f_1_sub_x_nonpos
        have add_nonpos: f x + f (1 - x) ≤ 0 := by linear_combination f_x_nonneg + f_1_sub_x_nonpos
        have add_eq_zero: f x + f (1 - x) = 0 := le_antisymm add_nonpos h'
        by_contra f_x_non_zero
        have f_x_neg: f x < 0 := lt_of_le_of_ne f_x_nonneg f_x_non_zero
        linarith
      -- Case \( x = 0 \): It has been proved above that \( f(0) = 0 \).
      | Or.inr h => rw [<-h, f_zero]
    have fract_x_range := Int.floor_eq_zero_iff.1 <| Int.floor_fract x'
    exact f_zero_to_one _ fract_x_range
  -- Prove that \( f(x) = \lfloor x \rfloor \) satisfies the three conditions in the problem.
  . constructor
    . intros x y
      constructor
      . have := Int.le_floor_add_floor x y
        norm_cast
        simp at this
        exact this
      . norm_cast
        exact Int.le_floor_add x y
    . constructor
      . intro x x_min x_max
        apply le_of_eq
        rw [Int.floor_eq_zero_iff]
        simp
        exact And.intro x_min x_max
      . norm_num
