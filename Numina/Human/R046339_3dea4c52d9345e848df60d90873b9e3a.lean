import Mathlib

/-Given the function $f(x)=x(x+k)(x+2k)(x-3k)$, and $f′(0)=6$, find the value of $k$.-/
theorem algebra_9369 {f : ℝ → ℝ} (hf : f = fun x => x * (x + k) * (x + 2 * k) * (x - 3 * k)) (h : deriv f 0 = 6) :
    k = -1 := by
  let g : ℝ → ℝ := fun x => (x + k) * (x + 2 * k) * (x - 3 * k)
  have hfg : f = fun x => x * g x := by
    ext x
    simp only [hf, g]
    ring
  -- Let $g(x)=(x+k)(x+2k)(x-3k)$, then $f(x)=xg(x)$.
  have df : ∀ x : ℝ, deriv f x = g x + x * deriv g x := by
    intro x
    rw [hfg]
    have gd : Differentiable ℝ g := by simp [g]
    have dmul := deriv_mul (differentiable_id' x) (gd x)
    simpa [deriv_id'', mul_one] using dmul
  -- $f'(x)=g(x)+xg'(x)$
  have : k ^ 3 = - 1 := by
    have := h ▸ df 0
    have hg : g 0 = - 6 * k ^ 3 := by simp only [g] ; ring
    simp only [hg, zero_add, zero_mul, add_zero, mul_zero, neg_add_cancel, zero_sub, neg_zero, mul_comm] at this
    -- Given that $f′(0)=6$, we have $g(0)=-6k^3=6$
    have : 6 / -6 = k ^ 3 := div_eq_of_eq_mul (by norm_num) this
    simpa only [ne_eq, eq_comm, OfNat.zero_ne_ofNat, not_false_eq_true, div_neg_self]
  rw [pow_eq_neg_one_iff] at this
  tauto
  -- Solving this for $k$ gives $k=-1$.
  -- So, the answer is $\boxed{B: -1}$.
