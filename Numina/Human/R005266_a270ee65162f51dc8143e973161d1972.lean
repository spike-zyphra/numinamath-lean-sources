import Mathlib

/-
Trouver toutes les fonctions $f$ de $\mathbb{R}$ dans $\mathbb{R}$ telles que pour tous réels $x, y$,

$$
f(x f(x)+f(y))=f(x)^{2}+y
$$
-/
theorem algebra_607261:
    {f :  ℝ → ℝ | ∀ x y, f (x * f x + f y) = (f x)^2 + y} = {fun x => x, fun x => -x} := by
  -- Prove set equality by proving mutual subset
  rw [subset_antisymm_iff, Set.subset_def, Set.subset_def]
  simp
  constructor
  . intro f hf
    -- set $x = 0$ in `hf`, we got $f(f(y)) = (f(0))^2 + y$
    have h1 : ∀ y, f (f y) = (f 0)^2 + y := by
      intro y
      have := hf 0 y
      simp at this
      exact this
    -- $f ∘ f$ is surjective
    have f_comp_f_surjective : Function.Surjective (f ∘ f) := by
      unfold Function.Surjective Function.comp
      intro b
      use b - (f 0)^2
      rw [h1]
      ring_nf
    -- so $f$ is surjective
    have f_surjective : Function.Surjective f := Function.Surjective.of_comp f_comp_f_surjective
    -- there exists $x$ such that $f(x) = 0$ because $f$ is surjective
    obtain ⟨zero_point, hzero_point⟩ := f_surjective 0
    -- setting $x = zero_point$ and $y = zero_point$, we can prove $f(0) = 0$
    have f_zero: f 0 = 0 := by
      have := hf zero_point zero_point
      simp [hzero_point] at this
      have h' := h1 0
      rw [this, hzero_point, add_zero] at h'
      symm at h'
      rw [sq_eq_zero_iff] at h'
      rw [h'] at hzero_point
      exact hzero_point
    -- we can prove $f(f(x)) = x$ in `h1`
    rw [f_zero] at h1
    simp at h1
    -- setting $(x, 0)$ and $(f(x), 0)$, we can prove $f^2(x) = x^2$
    have f_sq_eq_x_sq: ∀ x, (f x) ^ 2 = x ^ 2 := by
      intro x
      have h' := hf x 0
      rw [f_zero, add_zero, add_zero] at h'
      have h'' := hf (f x) 0
      rw [f_zero, add_zero, add_zero, h1, mul_comm] at h''
      rw [<-h', <-h'']
    -- at each point $x$, $f(x) = x \or f(x) = -x$
    have f_x_id_or_neg : ∀ x, f x = x ∨ f x = -x := by
      intro x
      have h' := f_sq_eq_x_sq x
      rw [sq_eq_sq_iff_eq_or_eq_neg] at h'
      exact h'
    -- prove $f(x) = x \or f(x) = -x$ by contradiction
    have f_id_or_neg : (∀ x, f x = x) ∨ (∀ x, f x = -x) := by
      by_contra h
      simp at h
      -- if there exists $a, b$ such that $f(a) = -a$ and $f(b) = b$
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
      replace ha' := f_x_id_or_neg a
      simp [ha] at ha'
      replace hb' := f_x_id_or_neg b
      simp [hb] at hb'
      -- set $x = b$ and $y = a$ in `hf`, we got $f(a^2 + b) = a^2 + b$
      have h' := hf b a
      simp [ha', hb'] at h'
      -- use `f_x_id_or_neg` to get $f(a^2 + b) = a^2 + b \or f(a^2 + b) = -a^2 - b$
      have h'' := f_x_id_or_neg (b * b + -a)
      simp [h'] at h''
      -- for each case, we can get a contradiction by $a = 0$ or $b = 0$
      cases h'' with
      | inl h'' =>
        rw [<-sub_eq_zero] at h''
        ring_nf at h''
        simp at h''
        rw [h''] at ha
        exact ha f_zero
      | inr h'' =>
        rw [<-sub_eq_zero] at h''
        ring_nf at h''
        simp at h''
        rw [h'', neg_zero] at hb
        exact hb f_zero
    -- in fact, `f_id_or_neg` is the same as the goal
    cases f_id_or_neg with
    | inl f_id =>
      left
      ext x
      exact f_id x
    | inr f_neg =>
      right
      ext x
      exact f_neg x
  -- prove these functions satisfy the equation
  . constructor
    all_goals intros; rw [<-sub_eq_zero]; ring_nf
