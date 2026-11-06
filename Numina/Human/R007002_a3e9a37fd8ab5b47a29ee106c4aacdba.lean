import Mathlib

/- vind alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ die voldoen aan

$$
f\left(x^{2} y\right)+2 f\left(y^{2}\right)=\left(x^{2}+f(y)\right) \cdot f(y)
$$

voor alle $x, y \in \mathbb{R}$. -/
/- Vind alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ die voldoen aan

$$
f\left(x^{2} y\right)+2 f\left(y^{2}\right)=\left(x^{2}+f(y)\right) \cdot f(y)
$$

voor alle $x, y \in \mathbb{R}$. -/
theorem algebra_604614 :
    {f : ℝ → ℝ | ∀ x y, f (x ^ 2 * y) + 2 * f (y ^ 2) = (x ^ 2 + f y) * f y} =
    {fun _ => 0, fun x => 2 * x, fun x => 2 * abs x} := by
  -- Prove set equality by proving mutual subset
  rw [subset_antisymm_iff, Set.subset_def, Set.subset_def]
  simp
  constructor
  . intros f hf
    -- substituting $x=1$
    have h1 (y: ℝ) : 2 * f (y ^ 2) = (f y) ^ 2 := by
      have h := hf 1 y
      simp at h
      rw [<-sub_eq_zero] at h
      rw [<-sub_eq_zero, <-h]
      ring_nf
    -- cancel $2 * f (y ^ 2)$ in the original functional equation
    replace hf : ∀ (x y : ℝ), f (x ^ 2 * y) = x ^ 2 * f y := by
      intro x y
      have := hf x y
      rw [h1] at this
      rw [<-sub_eq_zero] at this
      rw [<-sub_eq_zero, <-this]
      ring_nf
    -- Substituting $y=1$ here gives $f\left(x^{2}\right)=x^{2} f(1)$， so $f(x) = f(1) * x$ for all $x \geq 0$
    have f_nonneg (x: ℝ) (x_nonneg: 0 ≤ x) : f x = f 1 * x:= by
      have := hf (Real.sqrt x) 1
      simp [x_nonneg] at this
      rw [mul_comm] at this
      exact this
    -- Substituting $y=-1$ here gives $f\left(-x^{2}\right)=x^{2} f(-1)$， so $f(x) = -f(-1) * x$ for all $x < 0$
    have f_neg (x: ℝ) (x_neg: x < 0) : f x = - f (-1) * x:= by
      have := hf (Real.sqrt (-x)) (-1)
      have neg_x_nonneg : 0 ≤ (-x) := by linarith
      simp [neg_x_nonneg] at this
      rw [this]
      ring_nf
    -- Substituting $y=1$ in `h1` gives $2 f(1)=f(1)^{2}$, so $f(1)=0 \or f(1)=2$
    have f_one : f 1 = 0 ∨ f 1 = 2 := by
      have := h1 1
      simp at this
      rw [sq, <-sub_eq_zero, <-sub_mul, mul_eq_zero, sub_eq_zero] at this
      exact this.by_cases (Or.inr ∘ Eq.symm) Or.inl
    -- Substituting $y=-1$ in `h1` gives $f^2(-1)=2*f(1)$
    have f_neg_one : f (-1) ^ 2 = 2 * f 1 := by
      have := h1 (-1)
      simp at this
      symm
      exact this
    -- consider the value of $f(1)$
    match f_one with
    | Or.inl f1_eq_0 =>
      left
      -- prove $f(-1) = 0$
      rw [f1_eq_0] at f_neg_one
      simp at f_neg_one
      -- prove $f(x) = 0$ for all $x$
      ext x
      by_cases h : 0 ≤ x
      . rw [f_nonneg x h, f1_eq_0, zero_mul]
      . simp at h; rw [f_neg x h, f_neg_one]; simp
    | Or.inr f1_eq_2 =>
      right
      -- substitute $f(1) = 2$ in `f_neg_one`, we get $f(-1) = -2 \or f(-1) = 2$
      replace f_neg_one : f (-1) = -2 ∨ f (-1) = 2 := by
        rw [f1_eq_2, <-sq, sq_eq_sq_iff_abs_eq_abs, Nat.abs_ofNat, abs_eq] at f_neg_one
        symm
        exact f_neg_one
        norm_num
      -- consider the value of $f(-1)$
      match f_neg_one with
      | Or.inl f_neg_1_eq_neg_2 =>
        -- prove $f(x) = 2 * x$ for all $x$
        left
        ext x
        by_cases h : 0 ≤ x
        . rw [f_nonneg x h, f1_eq_2]
        . simp at h; rw [f_neg x h, f_neg_1_eq_neg_2]; simp
      | Or.inr f_neg_1_eq_2 =>
        -- prove $f(x) = 2 * |x|$ for all $x$
        right
        ext x
        by_cases h : 0 ≤ x
        . rw [f_nonneg x h, f1_eq_2, abs_of_nonneg h]
        . simp at h; rw [f_neg x h, f_neg_1_eq_2, abs_of_neg h]; simp
  constructor
  -- verify the three functions satisfy the functional equation
  . intros x y
    ring_nf
  . intro x y
    rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
    ring_nf
    rw [sq_abs]
