import Mathlib

/- Bepaal alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ zodat

$$
(y+1) f(x)+f(x f(y)+f(x+y))=y
$$

voor alle $x, y \in \mathbb{R}$. -/
theorem algebra_606065: {f : ℝ → ℝ | ∀ x y, (y + 1) * f x + f (x * f y + f (x + y)) = y} = {fun x => -x} := by
  apply Set.eq_of_subset_of_subset
  all_goals simp
  . intro f hf
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
    -- since f is injective, we have $x * f (-1) + f (x - 1) = f (-1)$
    have f_neg_1_eq_neg_1 : ∀ x, x * f (-1) + f (x - 1) = f (-1) := by
      intro x
      have := f_bijective.injective
      unfold Function.Injective at this
      apply this
      exact hf_y_eq_neg_1 x
    -- set $x = x + 1$ in `f_neg_1_eq_neg_1`, we get $f(x)=-f(-1)f(x)$
    have f_linear : ∃ c : ℝ , ∀ x, f x = c * x := by
      use -f (-1)
      intro x
      have h := f_neg_1_eq_neg_1 (x + 1)
      simp at h
      linear_combination h
    obtain ⟨c, f_linear_eq⟩ := f_linear
    -- substitute $f(x) = c * x$ in the original equation at $(1, 0)$
    have c_values_1 : c = 0 ∨ c = -1 := by
      have h := hf 1 0
      simp [f_linear_eq] at h
      rw [<-mul_one_add, mul_eq_zero] at h
      match h with
      | Or.inl h => left; exact h
      | Or.inr h => right; linear_combination h
    -- substitute $f(x) = c * x$ in the original equation at $(0, 1)$
    have c_values_2 : c = 1 ∨ c = -1 := by
      have h := hf 0 1
      simp [f_linear_eq] at h
      rw [<-sq, sq_eq_one_iff] at h
      exact h
    -- so we have $c = -1$
    have c_eq_neg_1 : c = -1 := by
      have := and_or_right.2 (And.intro c_values_1 c_values_2)
      simp at this
      match this with
      | Or.inl h => linarith only [h]
      | Or.inr h => exact h
    -- so $f(x) = -x$
    ext x
    rw [f_linear_eq, c_eq_neg_1]
    simp
  -- check that $f(x) = -x$ is a solution
  . intro x y
    ring
