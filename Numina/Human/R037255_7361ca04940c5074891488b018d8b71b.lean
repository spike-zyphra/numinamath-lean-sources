import Mathlib

/-If $f(x)=ax+b$ and $f^{-1}(x)=bx+a$ with $a$ and $b$ real, what is the value of $a+b$?-/
theorem algebra_10579 {a b : ℝ} {f f_inv : ℝ → ℝ} (hf : f = fun x => a * x + b)
    (hf_inv : f_inv = fun x => b * x + a) (h: ∀x, f (f_inv x) = x) : a + b = -2 := by
  -- Since f(f^{-1}(x))=x, it follows that a(bx+a)+b=x
  have : ∀x, a * (b * x + a) + b = x := by
    intro x
    have := h x
    rw [hf, hf_inv] at this
    simp at this
    exact this

  -- which implies $abx + a^2 +b = x$,
  have eq : ∀x, a * b * x + a ^ 2 + b = x := by
    intro x
    rw (config := { occs := .pos [2]}) [(this x).symm]
    ring_nf

  -- This equation holds for all values of $x$ only if $ab=1$ and $a^2+b=0$.
  -- a * b * 0 + a ^ 2 + b = 0
  have h1 := eq 0
  -- a ^ 2 + b = 0
  simp at h1
  -- a * b * 1 + a ^ 2 + b = 1
  have h2 := eq 1
  -- a * b = 1
  rw [add_assoc, h1] at h2
  simp at h2

  -- Then $b = -a^2$.
  rw [add_comm, ←sub_neg_eq_add, sub_eq_zero] at h1
  -- Substituting into the equation $ab = 1$, we get $-a^3 = 1$.
  rw [h1, mul_neg, mul_comm, ←pow_succ, two_add_one_eq_three] at h2
  -- because a is real number, a = -1
  have ha : a = -1 := by
    have : a^3 + 1 = 0 := by linarith
    have : (a + 1) * (a^2 - a + 1) = 0 := by linarith
    simp at this
    rcases this with h1 | h2
    . -- a + 1 = 0
      linarith
    . -- a^2 - a + 1 = 0, it is impossible, because a^2 - a + 1 > 0
      have : ∃r, a = r + 1/2 := by
        use (a - 1/2)
        simp
      rcases this with ⟨r, hr⟩
      rw [hr] at h2
      ring_nf at h2
      have :  r ^ 2 ≥ 0 := by exact sq_nonneg r
      linarith
  -- so, b = -1
  rw [h1, ha]
  linarith
