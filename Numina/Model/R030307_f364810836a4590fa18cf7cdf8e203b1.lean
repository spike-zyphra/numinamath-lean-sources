import Mathlib

theorem algebra_606065: {f : ℝ → ℝ | ∀ x y, (y + 1) * f x + f (x * f y + f (x + y)) = y} = {fun x => -x} := by
  ext f
  simp
  constructor
  . intro hf
    -- we can rewrite the equalition as `hf_x_eq_zero`
    have hf_x_eq_zero : ∀ y, f (f y) = y * (1 - f 0) - f 0 := by
      intro y
      have h := hf 0 y
      simp at h
      linear_combination h
    -- when $f(0) ≠ 1$, we can prove that $f$ is bijective
    have f_bijective_f_0_ne_1 (f0_ne_1: f 0 ≠ 1): Function.Bijective f := by
      -- we can prove that f ∘ f is bijective beacuse f ∘ f is linear
      have : Function.Bijective (f ∘ f) := by
        have f0_ne_1': 1 - f 0 ≠ 0 := by
          intro m
          rw [sub_eq_zero] at m
          rw [m] at f0_ne_1
          simp at f0_ne_1
        constructor
        . unfold Function.Injective Function.comp
          intros x y h
          rw [hf_x_eq_zero x, hf_x_eq_zero y] at h
          simp at h
          simp [f0_ne_1'] at h
          exact h
        . unfold Function.Surjective Function.comp
          intro y
          use ((y + f 0) / (1 - f 0))
          rw [hf_x_eq_zero]
          simp [f0_ne_1']
      -- we can prove that f is bijective because f ∘ f is bijective
      constructor
      . exact Function.Injective.of_comp this.injective
      . exact Function.Surjective.of_comp this.surjective
    -- consider the case when $f(0) = 1$
    have f_bijective_f_0_eq_1 (f0_eq_1: f 0 = 1): Function.Bijective f := by
      -- we get $f(f(x)) = -1$
      rw [f0_eq_1] at hf_x_eq_zero
      simp at hf_x_eq_zero
      -- substitute $y = 0$ in the original equation
      have hf_y_eq_zero : ∀ x, f (x + f x) = - f x := by
        intro x
        have h := hf x 0
        simp [f0_eq_1] at h
        linear_combination h
      -- substitute $x = f(z)$ and $y = z$ in the original equation
      have hf_x_eq_fz : ∀ z, f ((f z) ^ 2 - f z) = 2 * z + 1 := by
        intro z
        have h := hf (f z) z
        nth_rw 4 [add_comm] at h
        rw [hf_y_eq_zero z, hf_x_eq_zero z] at h
        simp at h
        rw [<-sq] at h
        linear_combination h
      let g := λ x : ℝ ↦ x ^ 2 - x
      have comp_comp: f ∘ g ∘ f = fun x => 2 * x + 1 := by
        ext x
        unfold Function.comp
        simp [g]
        exact hf_x_eq_fz x
      -- (f ∘ g ∘ f) is bijective beacuse it is linear
      have : Function.Bijective (f ∘ g ∘ f) := by
        rw [comp_comp]
        constructor
        . unfold Function.Injective
          intros x y h
          simp at h
          exact h
        . unfold Function.Surjective
          intro y
          use ((y - 1) / 2)
          simp
          ring_nf
      -- we can prove that f is bijective because (f ∘ g ∘ f) is bijective
      constructor
      . exact Function.Injective.of_comp <| Function.Injective.of_comp this.injective
      . exact Function.Surjective.of_comp this.surjective
    -- so f is bijective
    have f_bijective: Function.Bijective f := by
      by_cases h: f 0 = 1
      . exact f_bijective_f_0_eq_1 h
      . exact f_bijective_f_0_ne_1 h
    -- substitute $y = -1$ in `hf_x_eq_zero`
    have f_f_neg_1 : f (f (-1)) = -1 := by
      specialize hf_x_eq_zero (-1)
      simp at hf_x_eq_zero
      exact hf_x_eq_zero
    -- substitute $y = -1$ in the original equation
    have hf_y_eq_neg_1 : ∀ x, f (x * f (-1) + f (x - 1)) = f (f (-1)) := by
      intro x
      have h := hf x (-1)
      simp at h
      nth_rw 3 [<-f_f_neg_1] at h
      linear_combination h
    -- since f is injective, we have $x \cdot f(-1) + f(x - 1) = f(-1)$
    have f_neg_1_eq_neg_1 : ∀ x, x * f (-1) + f (x - 1) = f (-1) := by
      intro x
      have := f_bijective.injective
      unfold Function.Injective at this
      apply this
      exact hf_y_eq_neg_1 x
    -- set $x = 1$ in `f_neg_1_eq_neg_1`, we get $f(0)=0$
    have hf0_eq0: f 0 = 0 := by
      specialize f_neg_1_eq_neg_1 1
      simp at f_neg_1_eq_neg_1
      linarith
    -- replace hf_x_eq_zero
    rw [hf0_eq0] at hf_x_eq_zero
    simp at hf_x_eq_zero
    -- set (x,y)=(t,0)
    have hf_x_eq_self : ∀ x, f (x) + f (f x) = 0 := by
      intro x
      have h := hf x 0
      simp [hf0_eq0] at h
      exact h
    -- able to prove that it is equal to negative
    funext x
    specialize hf_x_eq_self x
    specialize hf_x_eq_zero x
    have : f x + x = 0 := by
      linarith [hf_x_eq_self, hf_x_eq_zero]
    linarith
  -- verify the answer
  . intro hf
    intro x y
    rw [hf]
    dsimp
    -- since $(y+1)(-x) - (-(x \cdot (-y) + (-(x+y)))) = -x(y+1) - (-xy -x - y) = -xy -x + xy +x +y = y$, we are done
    ring_nf