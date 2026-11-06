import Mathlib

/- Vind alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ met

$$
f(x+y f(x+y))=y^{2}+f(x) f(y)
$$

voor alle $x, y \in \mathbb{R}$. -/
theorem algebra_605157:
    {f :  ℝ → ℝ | ∀ x y, f (x + y * f (x + y)) = y ^ 2 + f x * f y} = {fun x => 1 - x, fun x => x + 1} := by
    -- Prove set equality by proving mutual subset
    rw [subset_antisymm_iff, Set.subset_def, Set.subset_def]
    simp
    constructor
    . intros f hf
      -- exists $x$ such that $f(x) \neq 0$, because otherwise $f(x)=0$ for all $x$.
      have : ∃ x, f x ≠ 0 := by
        by_contra h
        simp at h
        have h' := hf 0 1
        simp only [h] at h'
        ring_nf at h'
        simp at h'
      obtain ⟨a, ha⟩ := this
      -- We can prove $f(0)=1$ by setting $x=a$ and $y=0$ in `hf`.
      have f0_eq_1: f 0 = 1 := by
        have h' := hf a 0
        simp only [add_zero, mul_zero] at h'
        ring_nf at h'
        simp [ha] at h'
        exact h'
      -- we can prove $f(1)=0 \or f(-1) = 0$ by setting $x = 1$ and $y = -1$
      have : f 1 = 0 ∨ f (-1) = 0 := by
        have h' := hf 1 (-1)
        simp only [neg_one_mul, neg_neg, one_mul, add_neg_cancel_left] at h'
        ring_nf at h'
        simp [f0_eq_1] at h'
        exact h'
      -- consider the two cases
      match this with
      | Or.inl f1_eq_0 =>
        left
        ext x
        -- setting $x = x$ and $y = 1 - x$ in `hf`,
        have h1 := hf x (1 - x)
        -- setting $x = 1 - x$ and $y = x$ in `hf`,
        have h2 := hf (1 - x) x
        -- simplify the two equations and subtract them, we got $ f(1 - x) =  f(x) - 1 + 2x$
        ring_nf at h1 h2
        rw [f1_eq_0] at h1 h2
        ring_nf at h1 h2
        have h3 : f (1 - x) = (f x) - 1 + x * 2 := by linear_combination (h2 - h1)
        -- substitute $f(1 - x)$ with $f(x)$ in `h1`, we got $(f(x) - (1 - x))^ 2 = 0$
        rw [h3, <-sub_eq_zero] at h1
        ring_nf at h1
        have h4 : (f x - (1 - x)) ^ 2 = 0 := by
          calc _ = - ( -1 + f x * 2 + (-(f x * x * 2) - f x ^ 2) + (x * 2 - x ^ 2)) := by ring_nf
            _ = 0 := by rw [h1, neg_zero]
        -- solve $(f(x) - (1 - x))^ 2 = 0$ to get $f(x) = 1 - x$
        simp at h4
        exact sub_eq_zero.1 h4
      | Or.inr f_neg_1_eq_0 =>
        right
        ext x
        -- setting $x = x$ and $y = -1 - x$ in `hf`,
        have h1 := hf x (-1 - x)
        -- setting $x = -1 - x$ and $y = x$ in `hf`,
        have h2 := hf (-1 - x) x
        -- simplify the two equations and subtract them, we got $ f(-1 - x) =  f(x) - 1 - 2x$
        ring_nf at h1 h2
        rw [f_neg_1_eq_0] at h1 h2
        ring_nf at h1 h2
        have h3 : f (-1 - x) = (f x) - 1 - x * 2 := by linear_combination (h2 - h1)
        -- substitute $f(-1 - x)$ with $f(x)$ in `h1`, we got $(f(x) - (x + 1))^ 2 = 0$
        rw [h3, <-sub_eq_zero] at h1
        ring_nf at h1
        have h4 : (f x - (x + 1)) ^ 2 = 0 := by
          calc _ = - (-1 + f x * 2 + (f x * x * 2 - f x ^ 2) + (-(x * 2) - x ^ 2)) := by ring_nf
            _ = 0 := by rw [h1, neg_zero]
        -- solve $(f(x) - (1 - x))^ 2 = 0$ to get $f(x) = 1 - x$
        simp at h4
        exact sub_eq_zero.1 h4
    -- check the other direction
    . constructor;
      all_goals intros x y; ring_nf
