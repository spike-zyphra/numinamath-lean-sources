import Mathlib

/-"Let $f : \mathbb{R} \to \mathbb{R}$ be a function such that
\[f(f(x - y)) = f(x) f(y) - f(x) + f(y) - xy\]for all $x,$ $y.$  Find the sum of all possible values of $f(1).$"
-/
theorem algebra_15427 {f : ℝ → ℝ} (h : ∀ x y, f (f (x - y)) = f x * f y - f x + f y - x * y) :
    f 1 = -1 := by
  -- Let $a = f(0)$ and $b = f(f(0))$.  Setting $y = x$ in the given equation, we get
  have ha : ∃a, a = f 0 := by simp
  have hb : ∃b, b = f (f 0) := by simp
  -- \[[f(x)]^2 - x^2 = b \quad (1)\]for all $x$.
  rcases hb with ⟨b, hb⟩
  have eq1 : ∀x, b = (f x)^2 - x^2 := by
    intro x
    have := h x x
    simp at this
    linarith
  -- In particular, for $x = 0$, $a^2 = b$.
  rcases ha with ⟨a, ha⟩
  have ha' : a^2 = b := by
    rw [eq1 0]
    rw [ha]
    simp

  -- Setting $y = 0$ in the given equation, we get
  -- \[f(f(x)) = (a - 1) f(x) + a \quad (2)\]for all $x$.
  have eq2 : ∀x, f (f x) = (a - 1) * f x + a := by
    intro x
    have := h x 0
    simp at this
    rw [this, ha]
    linarith

  -- Substituting $f(x)$ for $x$ in equation (1), we get
  -- \[[f(f(x))]^2 - [f(x)]^2 = b.\]
  have eq3 : ∀x, (f (f x))^2 - (f x)^2 = b := by
    intro x
    exact (eq1 (f x)).symm

  --But from equation (2), $[f(f(x))]^2 = [(a - 1) f(x) + a]^2 = (a^2 - 2a + 1) [f(x)]^2 + 2a(a - 1) f(x) + a^2$
  have eq3' : ∀x, (f (f x))^2 = (a^2 - 2 * a + 1) * (f x)^2 + 2 * a * (a - 1) * f x + a^2 := by
    intro x
    rw [eq2 x]
    ring_nf

  -- so \[(a^2 - 2a) [f(x)]^2 + 2a(a - 1) f(x) = af(x) [(a - 2) f(x) + 2(a - 1)] = 0\]for all $x$.
  have eq3'' : ∀x, b - a^2 = a * f x * ((a - 2) * f x + 2 * (a - 1)) := by
    intro x
    rw [(eq3 x).symm, eq3' x]
    ring_nf
  rw [ha'] at eq3''
  -- If $a \neq 0$
  by_cases ha'' : a ≠ 0
  . -- then \[f(x) [(a - 2) f(x) + 2(a - 1)] = 0\]for all $x$
    have eq3'' : ∀x, f x * ((a - 2) * f x + 2 * (a - 1)) = 0 := by
      intro x
      have := eq3'' x
      simp at this
      rcases this with (⟨ha | hf⟩ | h)
      . -- a = 0, which conflicts with our assumption.
        absurd ha''
        exact ha
      . -- f x = 0
        rw [hf]
        simp
      . -- (a - 2) * f x + 2 * (a - 1) = 0
        rw [h]
        simp

    -- so $f(x)$ attains at most two different values.
    have := eq3'' 0
    rw [ha.symm] at this
    simp at this
    rcases this with (r₁ | r₂)
    . -- a = 0, which conflicts with our assumption.
      absurd ha''
      exact r₁
    -- (a - 2) * a + 2 * (a - 1) = 0 ↔ a^2 = 2 = b
    ring_nf at r₂
    rw [ha'] at r₂
    have r₂: b = 2 := by linarith
    have p := eq1 1
    rw [r₂] at p
    -- p: (f 1)^2 - 1 = 2, which means $f(1) ≠ 0$.
    have eq3'' := eq3'' 1
    simp at eq3''
    rcases eq3'' with (r₃ | r₄)
    . -- f 1 = 0, conflicts with `(f 1)^2 - 1 = 2`.
      rw [r₃] at p
      linarith
    -- from p, f 1 = √3 or f 1 = -√3
    have p : (f 1 - √3) * (f 1 + √3) = 0 := by
      ring_nf
      rw [Real.sq_sqrt]
      repeat linarith
    simp at p

    -- from a^2 = 2, we have a = ±√2
    have : (a - √2) * (a + √2) = 0 := by
      ring_nf
      rw [Real.sq_sqrt]
      repeat linarith
    simp at this
    have one_lt_sqrt2 : 1 < √2 := by
      apply (Real.lt_sqrt (by linarith)).mpr
      linarith
    have two_lt_sqrt6 : 2 < √6 := by
      apply (Real.lt_sqrt (by linarith)).mpr
      linarith
    have s3ms2 : √3 * √2 = √6 := by
      have : (6 : ℝ) = 3 * 2 := by linarith
      rw [this, Real.sqrt_mul]
      positivity
    -- this part is only a boring calculation.
    rcases p with (r₅ | r₆)
    . -- f 1 = √3
      have r₅ : f 1 = √3 := by linarith
      rw [r₅] at r₄
      rcases this with (r₇ | r₈)
      . -- a = √2
        have r₇ : a = √2 := by linarith
        rw [r₇] at r₄
        have : (√2 - 2) = -√2 * (√2 - 1) := by
          ring_nf
          rw [Real.sq_sqrt]
          linarith
          positivity
        rw [this, mul_comm, ←mul_assoc] at r₄
        have r₄ : (√2 - 1) * (√3 * -√2 + 2) = 0 := by linarith
        simp at r₄
        induction r₄
        . linarith
        . rename_i r
          rw [s3ms2] at r
          linarith
      . -- a = -√2
        have r₈ : a = -√2 := by linarith
        rw [r₈] at r₄
        have : (-√2 - 2) = √2 * (-√2 - 1) := by
          ring_nf
          rw [Real.sq_sqrt]
          linarith
          positivity
        rw [this, mul_comm, ←mul_assoc] at r₄
        have r₄ : (- √2 - 1) * (√3 * √2 + 2) = 0 := by linarith
        simp at r₄
        induction r₄
        . linarith
        . rename_i r
          rw [s3ms2] at r
          linarith
    . -- f 1 = -√3
      have r₆ : f 1 = -√3 := by linarith
      rw [r₆] at r₄
      rcases this with (r₇ | r₈)
      . -- a = √2
        have r₇ : a = √2 := by linarith
        rw [r₇] at r₄
        have : (√2 - 2) = -√2 * (√2 - 1) := by
          ring_nf
          rw [Real.sq_sqrt]
          linarith
          positivity
        rw [this, mul_comm, ←mul_assoc] at r₄
        have r₄ : (√2 - 1) * (-√3 * -√2 + 2) = 0 := by linarith
        simp at r₄
        induction r₄
        . linarith
        . rename_i r
          rw [s3ms2] at r
          linarith
      . -- a = -√2
        have r₈ : a = -√2 := by linarith
        rw [r₈] at r₄
        have : (-√2 - 2) = √2 * (-√2 - 1) := by
          ring_nf
          rw [Real.sq_sqrt]
          linarith
          positivity
        rw [this, mul_comm, ←mul_assoc] at r₄
        have r₄ : (- √2 - 1) * (-√3 * √2 + 2) = 0 := by linarith
        simp at r₄
        induction r₄
        . linarith
        . rename_i r
          rw [s3ms2] at r
          linarith

  -- Hence, $a = 0$, then $b = 0$
  simp at ha''
  rw [ha''] at ha'
  -- so from equation (1), \[[f(x)]^2 = x^2,\]which means $f(x) = x$ or $f(x) = -x$ for all $x$.
  rw [ha'.symm] at eq1 eq3
  rw [ha''] at eq2
  simp at eq1
  -- Let $x$ be a value such that $f(x) = x$.
  -- Then $f(f(x)) = f(x) = x$, so by equation (2), $x = -x$, or $x = 0$.
  -- Hence, the only value of $x$ such that $f(x) = x$ is $x = 0$.
  -- Therefore, $f(x) = -x$ for all $x$.  It is easy to check that this solution works.
  have eq1 : ∀x, f x = -x ∨ f x = x := by
    intro x
    have := eq1 x
    have : (f x - x) * (f x + x) = 0 := by linarith
    simp at this
    rcases this with (r₁ | r₂)
    . apply Or.inr
      linarith
    . apply Or.inl
      linarith
  -- Therefore, the sum of all possible values of $f(1)$ is $\boxed{-1}
  have := eq1 1
  rcases this with (r₁ | r₂)
  . exact r₁
  have := eq2 1
  simp at this
  rw [r₂] at this
  linarith
