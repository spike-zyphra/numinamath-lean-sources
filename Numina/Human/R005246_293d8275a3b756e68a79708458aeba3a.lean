import Mathlib

/- Let R denote the set of all real numbers. Find all functions $f$ from R to R satisfying:
(i) there are only finitely many $s$ in R such that $f(s)=0$, and
(ii) $f\left(x^{4}+y\right)=x^{3} f(x)+f(f(y))$ for all $x, y$ in $\mathbf{R}$. -/
theorem algebra_607118 :
  {f : ℝ → ℝ | {s | f s = 0}.Finite ∧ ∀ x y, f (x ^ 4 + y) = x ^ 3 * f x + f (f y)} = {id} := by
  ext f
  simp
  constructor
  -- First, we verify that f(x) = x is a solution.
  swap
  . rintro rfl
    simp
    intro x
    ring
  -- Now, we show that any solution must be f(x) = x.
  . rintro ⟨hfz, H⟩
    -- Setting (x, y) = (1, 0), we get f(f(0)) = 0.
    have h₁ := H 1 0
    simp at h₁
    -- Setting x = 0, we get f(f(y)) = f(y).
    have h₂ := H 0
    simp at h₂
    -- So f(0) = 0.
    rw [← h₂] at h₁
    -- Simplify f(f(y)) = f(y) in the original equation, we get f(x ^ 4 + y) = x ^ 3 * f(x) + f(y).
    have h₃ (x y) : f (x ^ 4 + y) = x ^ 3 * f x + f y := by rw [H, ← h₂]
    -- So f(x ^ 4) = x ^ 3 * f(x) by setting y = 0.
    have h₄ x := h₃ x 0
    simp [h₁] at h₄
    -- And we get f(x ^ 4 + y) = f(x ^ 4) + f(y).
    replace h₃ (x y) : f (x ^ 4 + y) = f (x ^ 4) + f y := by rw [h₃, h₄]
    -- We show that f is an odd function.
    have h₅ x : f (-x) = -f x := by
      -- If x = 0, we have f(0) = 0.
      wlog hx : x ≠ 0
      {
        simp at hx
        simp [hx, h₁]
      }
      -- If x ≠ 0, we have:
      --   f(-x)
      -- = -f((-x) ^ 4) / (-x) ^ 3
      -- = -f(x ^ 4) / x ^ 3
      -- = -f(x)
      calc f (-x)
        _ = f ((-x) ^ 4) / (-x) ^ 3 := by
          field_simp [show -x ≠ 0 from neg_ne_zero.mpr hx]
          linear_combination -h₄ (-x)
        _ = -f (x ^ 4) / x ^ 3 := by ring_nf
        _ = -f x := by
          field_simp
          linear_combination h₄ x
    -- We show that f is an additive function.
    have h₆ (a b) : f (a + b) = f a + f b := by
      -- WLOG, we may assume a ≥ 0.
      wlog ha : a ≥ 0 generalizing a b with K
      {
        -- If a < 0, we can use the odd property to reduce to the case a ≥ 0.
        --   f(a + b)
        -- = -f(-(a + b))
        -- = -f(-a - b)
        -- = -(f(-a) + f(-b))
        -- = -(-f a + -f b)
        -- = f a + f b
        calc f (a + b)
          _ = -f (-(a + b)) := by rw [h₅]; simp
          _ = -f (-a + -b) := by ring_nf
          _ = -(f (-a) + f (-b)) := by rw [K _ _ (by linarith)]
          _ = -(-f a + -f b) := by rw [h₅, h₅]
          _ = f a + f b := by ring
      }
      -- Now, we assume a ≥ 0.
      -- Set x = a ^ (1 / 4), we have a = x ^ 4.
      have ⟨x, hx⟩ : ∃ x, a = x ^ 4 := by
        use a ^ (1 / 4 : ℝ)
        rw [← Real.rpow_mul_natCast ha]
        simp
      -- So we have:
      --   f(a + b)
      -- = f(x ^ 4 + b)
      -- = f(x ^ 4) + f(b)
      -- = f(a) + f(b)
      calc f (a + b)
        _ = f (x ^ 4 + b) := by rw [hx]
        _ = f (x ^ 4) + f b := by rw [h₃]
        _ = f a + f b := by rw [hx, h₄]
    -- Now we show that the only zero of f is 0.
    have h₇ {x} (hx : f x = 0) : x = 0 := by
      -- If otherwise, say there is some x ≠ 0 such that f x = 0.
      by_contra! hx'
      -- We show that there are infinitely many s such that f s = 0, contradicting the assumption that f has only finitely many zeroes.
      let s (n : ℕ) := n * x
      absurd hfz
      -- We show that n * x are all zeroes of f and are all distinct.
      apply Set.infinite_of_injective_forall_mem (f := s)
      . -- We show that n * x are all distinct, which is simple.
        intro n m h
        simp [s, hx'] at h
        exact h
      . -- We show that n * x are all zeroes of f.
        -- We induct on n.
        intro n
        simp [s]
        induction n with
        | zero => simp [h₁]
        | succ n ih =>
          -- Simplify.
          rify
          ring_nf
          -- Use the additive property and the inductive hypothesis.
          simp [h₆, ih, hx]
    -- We show that f is injective.
    have h₈ : f.Injective := by
      -- If f(x) = f(y)
      intro x y h
      -- We know f(x) = f(x - y) + f(y)
      rw [show x = x - y + y by ring] at h
      rw [h₆] at h
      simp at h
      -- So f(x - y) = 0
      specialize h₇ h
      -- So x - y = 0 and x = y.
      exact sub_eq_zero.1 h₇
    -- Now from the equation f(y) = f(f(y)), we get f(x) = x for all x by injectivity.
    ext x
    simp
    apply_fun f
    exact (h₂ x).symm
