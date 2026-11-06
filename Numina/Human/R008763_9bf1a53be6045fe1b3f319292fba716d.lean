import Mathlib

/- Find all $a \in \mathbb{R}$ for which there exists a function $f: \mathbb{R} \rightarrow \mathbb{R}$, such that

(i) $f(f(x))=f(x)+x$, for all $x \in \mathbb{R}$,

(ii) $f(f(x)-x)=f(x)+$ ax, for all $x \in \mathbb{R}$. -/
theorem algebra_608032:
    {a : ℝ | ∃ f : ℝ → ℝ, (∀ x, f (f x) = f x + x) ∧ (∀ x, f (f x - x) = f x + a * x)} =
    {(1 + Real.sqrt 5) / 2, (1 - Real.sqrt 5) / 2} := by
    rw [subset_antisymm_iff, Set.subset_def, Set.subset_def]
    simp
    constructor
    . intro a f hf1 hf2

      -- Move \( f(x) \) in `hf1` to the other side, then apply an outer layer of \( f(x) \).
      -- We get \( f(f(f(x)) - f(x)) = f(x) \).
      have h1 (x:ℝ): f (f x) - f x = x := by rw [hf1]; ring_nf
      replace h1 := fun x => congr_arg f (h1 x)

      -- Set $x = f(x)$ in `hf2`
      -- We get $f(f(f(x)) - f(x)) = f(f(x)) + a f(x)$
      have h2 (x:ℝ) := hf2 (f x)
      -- The left hand side of `h1` and `h2` are equal, so the right hand side must be equal.
      have h3 (x:ℝ): f x = f (f x) + a * f x := by rw [<-h2, h1]
      -- Move \( f(x) \) to the other side
      replace h3 (x:ℝ):  f (f x) = (1 - a) * f x := by linear_combination -(h3 x)
      -- We know \( f(f(x)) = f(x) + x \), so we can substitute that in `hf1`
      have h4 (x:ℝ): a * f x = - x := by
        specialize hf1 x
        specialize h3 x
        rw [h3] at hf1
        linear_combination -hf1
      -- we get \( f(x) = - x / a \)
      -- if \( a = 0 \), then \( f(x) = 0 \), which is not a solution
      have h5 (x:ℝ): f x = - x / a ∧ a ≠ 0 := by
        by_cases h : a = 0
        . specialize h4 1
          rw [h] at h4
          simp at h4
        . specialize h4 x
          rw [mul_comm] at h4
          symm at h4
          rw [<-div_eq_iff h] at h4
          symm at h4
          exact And.intro h4 h
      have h6 (x:ℝ): f x = - x / a := (h5 x).1
      have h7 : a ≠ 0 := (h5 0).2

      -- substitute \( f(x) = - x / a \) in `h3`, we can get a quadratic equation
      have h6 : 1 * (a * a) + (-1) * a + -1 = 0 := by
        specialize h3 1
        rw [h6, h6] at h3
        ring_nf at h3
        replace h3 := congr_arg (fun x => x * a * a) h3
        simp only [] at h3
        rw [sq, sub_mul, inv_mul_cancel₀ h7] at h3
        conv at h3 =>
          lhs
          conv => arg 1; rw [mul_assoc, inv_mul_cancel₀ h7, mul_one]
        simp [inv_mul_cancel₀ h7] at h3
        linear_combination -h3
      -- solve the discrim of quadratic equation
      have discrim_sqrt: discrim (1:ℝ) (-1) (-1) = Real.sqrt 5 * Real.sqrt 5 := by
        unfold discrim
        ring_nf
        rw [Real.sq_sqrt]
        norm_num
      -- solve the quadratic equation
      rw [quadratic_eq_zero_iff one_ne_zero discrim_sqrt a] at h6
      simp at h6
      exact h6
    -- check whether the two solutions are valid
    . constructor
      -- we know \( f(x) = - x / a \) is a solution
      on_goal 1 => use (fun x => - (√5 - 1) / 2 * x)
      on_goal 2 => use (fun x => (√5 + 1) / 2 * x)
      -- simplify the goal
      all_goals
        simp
        constructor
        all_goals
          intro x
          ring_nf
          rw [Real.sq_sqrt]
          ring_nf
          norm_num
