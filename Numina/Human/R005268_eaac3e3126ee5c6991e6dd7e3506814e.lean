import Mathlib

/-
Trouver toutes les fonctions $\mathrm{f}: \mathbb{R} \rightarrow \mathbb{R}$ telles que pour tous réels $x, y$,

$$
(f(x)+y)(f(x-y)+1)=f(f(x f(x+1))-y f(y-1))
$$-/
theorem algebra_607261:
    {f :  ℝ → ℝ | ∀ x y, (f x + y) * (f (x - y) + 1) = f (f (x * f (x + 1)) - y * f (y - 1))} = {fun x => x} := by
  -- Prove set equality by proving mutual subset
  rw [subset_antisymm_iff, Set.subset_def, Set.subset_def]
  simp
  symm
  constructor
  . ring_nf
    simp
  . intro f hf
    -- set $y=0$ in `hf`, we got $f(f(xf(x+1))) = f(x)(f(x)+1)$
    have h1 : ∀ x, f (f (x * f (x + 1))) = f x * (f x + 1) := by
      intro x
      have := hf x 0
      simp at this
      symm
      exact this
    -- By setting $x=0\and y = -f (0)$, we can find a root of $f$
    have : ∃ x, f x = 0 := by
      have := hf 0 (-f 0)
      simp at this
      use f 0 + f 0 * f (-f 0 - 1)
      exact Eq.symm this
    obtain ⟨z, hz⟩ := this

    -- set $x = z \and y = z + 1$ in `h1`, we got $z = -1 \or f(-1) = -1$
    -- and we can find contradiction by setting $x=0\and y=1$ in `hf` when $z = -1$. So $f(-1) = -1$
    have f_neg_1 : f (-1) = -1 := by
      have := hf z (z + 1)
      simp [hz, h1] at this
      match this with
      | Or.inl z_eq_neg_one =>
        replace z_eq_neg_one : z = -1 := by linear_combination z_eq_neg_one
        rw [z_eq_neg_one] at hz
        have h' := hf 0 1
        simp [h1, hz, h'] at h'
      | Or.inr h => linear_combination h

    -- set $x = 0\and y=1$ in `hf`, we got $f(0)=0$
    have f_0 : f 0 = 0 := by
      have := hf 0 1
      simp [f_neg_1] at this
      exact Eq.symm this

    -- setting $x = 0$ in `hf` and setting $x = -1$ in `h1`, we got $y(f(-y) + 1) = (y - 1)(f(-1 - y) + 1)$
    have h2 (y:ℝ): y * (f (-y) + 1) = (y - 1) * (f (-1 - y) + 1) := by
      have h' := hf 0 y
      have h'' := hf (-1) y
      simp [f_0, f_neg_1] at h'
      simp [f_0, f_neg_1] at h''
      linear_combination h' - h''

    -- setting $y = 1$ in `hf`
    have hf_y_1 : ∀ x, (f (x - 1) + 1) * (f x + 1) = f x * (f x + 1) := by
      intro x
      have h' := hf x 1
      simp [f_0, h1] at h'
      rw [mul_comm] at h'
      exact h'

    -- setting $y = 1$ in `hf` and `y = -x` in `this`, we can prove that there is only one root of $f$
    have f_0_iff {x: ℝ} : f x = 0 ↔ x = 0 := by
      constructor
      . intro h
        have h' := hf_y_1 x
        simp [h] at h'
        have h'' := h2 (-x)
        simp [f_0, h] at h''
        nth_rw 2 [add_comm ] at h''
        rw [<-sub_eq_add_neg, h', mul_zero, neg_eq_zero] at h''
        exact h''
      . intro h
        rw [h]
        exact f_0
    -- we can prove $f(x) = -1 ↔ x = -1$ from `h1`
    have f_neg_one_iff {x: ℝ} : f x = -1 ↔ x = -1 := by
      constructor
      . intro h
        have := h1 x
        simp [h, f_0_iff] at this
        match this with
        | Or.inl x_eq_zero => linarith only [h, f_0_iff.2 x_eq_zero]
        | Or.inr h => linear_combination h
      . intro h
        rw [h]
        exact f_neg_1

    -- setting $x = 1$ in `hf_y_1`, we can prove $f(1) = 1$
    have f_1 : f 1 = 1 := by
      have := hf_y_1 1
      simp [f_0] at this
      rw [<-sub_eq_zero, <-one_sub_mul, mul_eq_zero] at this
      cases this with
      | inl h => linear_combination -h
      | inr h =>
        replace h : f 1 = -1 := by linear_combination h
        linarith only [f_neg_one_iff.1 h]

    -- setting $x = 2$ in `hf_y_1`, we can prove $f(2) = 2$
    have f_2 : f 2 = 2 := by
      have := hf_y_1 2
      simp [f_0, f_1] at this
      ring_nf at this
      rw [f_1] at this
      ring_nf at this
      cases this with
      | inl h => exact Eq.symm h
      | inr h =>
        replace h : f 2 = -1 := by linear_combination h
        linarith only [f_neg_one_iff.1 h]

    -- setting $x = -2$ in `h1`, we can prove $f(-2) = -2$
    have f_neg_2 : f (-2) = -2 := by
      have := h1 (-2)
      ring_nf at this
      simp [f_neg_1, f_2] at this
      replace : (f (-2) - (-2)) * (f (-2) - 1) = 0 := by linear_combination -this
      rw [mul_eq_zero, sub_eq_zero, sub_eq_zero] at this
      -- $f(-2) = -2$ or $f(-2) = 1$
      -- if $f(-2) = 1$, we can get $f(-3) = 0$ by setting $x = -2$ in `hf_y_1`
      cases this with
      | inl h => exact h
      | inr h =>
        have := hf_y_1 (-2)
        simp [h] at this
        linarith only [f_0_iff.1 this]

    -- cancel $f(x) + 1$ in `hf_y_1`
    -- if $f(x) = -1$, we can get $x = -1$, so $f(-1) = f(-2) + 1$
    have f_sub_1 {x: ℝ} : f x = f (x - 1) + 1 := by
      have := hf_y_1 x
      rw [<-sub_eq_zero, <-sub_mul, mul_eq_zero, sub_eq_zero] at this
      cases this with
      | inl h => exact Eq.symm h
      | inr h =>
        replace h : f x = -1 := by linear_combination h
        replace h := f_neg_one_iff.1 h
        rw [h]
        ring_nf
        rw [f_neg_1, f_neg_2]
        norm_num


    -- finally, we can prove $f(x) = x$ by set $x = -x$ in `h2`
    -- and simplify the equation with `f_sub_1
    ext x
    have := h2 (-x)
    simp at this
    rw [show -1 + x = x - 1 by ring, <-f_sub_1, <-sub_eq_zero] at this
    ring_nf at this
    linear_combination this
