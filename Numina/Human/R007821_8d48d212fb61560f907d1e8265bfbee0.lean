import Mathlib
/-A function $f(x)$ is defined for all real numbers $x$. For all non-zero values $x$, we have
\[2f\left(x\right) + f\left(\frac{1}{x}\right) = 5x + 4\]
Let $S$ denote the sum of all of the values of $x$ for which $f(x) = 2004$. Compute the integer nearest to $S$.-/
theorem algebra_13229 {f : ℝ → ℝ} (h : ∀ x, x ≠ 0 → 2 * f x + f (1 / x) = 5 * x + 4)
  (S : ℝ) (hS : S = ∑ᶠ x ∈ {x | f x = 2004}, x) :
  round S = 601 := by
    -- Substituting $\frac{1}{x}$, we have
    -- \[2f\left(\frac 1x\right) + f\left(x\right) = \frac{5}{x} + 4\]
    have h1 : ∀ x, x ≠ 0 → 2 * f (1 / x) + f x = 5 / x + 4 := by
      intro x hx
      have : 1 / x ≠ 0 := one_div_ne_zero hx
      convert h (1 / x) this using 1 <;> simp
      ring_nf
    -- This gives us two equations, which we can eliminate $f\left(\frac 1x\right)$ from (the first equation multiplied by two, subtracting the second):
    --  3f(x) = 10x + 4 - \frac 5x
    have h2 : ∀ x, x ≠ 0 → 3 * f x = 10 * x + 4 - 5 / x := by
      intro x hx
      have := h x hx
      have := h1 x hx
      linarith
    -- So we get when $x$ is not zero $f x = 2004 $ iff  $3 * 2004 * x = 10 * x^2 + 4 * x - 5$.
    have h3 : ∀ x ≠ 0, 3 * 2004 * x = 10 * x^2 + 4 * x - 5 ↔ f x = 2004 := by
      intro x hx
      have h2' := h2 x hx
      field_simp [add_mul] at h2'
      rw [mul_assoc 10, ←pow_two] at h2'
      constructor <;> intro h
      · rw [←h2'] at h
        nlinarith
      · rw [h] at h2'
        exact h2'
    rw [hS]
    -- Solve the quadratic $3 * 2004 * x = 10 * x ^ 2 + 4 * x - 5$.
    have hroots : {x | 3 * 2004 * x = 10 * x ^ 2 + 4 * x - 5} = {1502 / 5 - 3 * √(501337 / 2) / 5, 1502 / 5 + 3 * √(501337 / 2) / 5} := by
      ext x
      simp
      constructor <;> intro h
      replace h : 10 * (x * x) + (-6008) * x + (-5) = 0 := by linarith
      have hdiscrim : discrim (10 : ℝ) (-6008) (-5) = (12 * √(501337 / 2)) * (12 * √(501337 / 2)) := by
        simp [discrim]
        ring_nf
        simp
        norm_num
      have := ((quadratic_eq_zero_iff (by simp) hdiscrim x).1 h).symm
      convert this using 1 <;>
        constructor <;> intro h <;> simp [h] <;> field_simp <;> ring
      rcases h with h | h <;> simp [h] <;> ring_nf <;> field_simp <;> ring
    -- auxiliary lemma : the sum of roots of 3 * 2004 * x = 10 * x ^ 2 + 4 * x - 5 are $\frac {6008} {10}$.
    have aux : ∑ᶠ (x : ℝ) (_ : x ∈ {x | 3 * 2004 * x = 10 * x ^ 2 + 4 * x - 5}), x = 6008 / 10 := by
      rw [hroots, finsum_mem_pair]
      field_simp
      ring
      intro hfalse
      field_simp at hfalse
      ring_nf at hfalse
      have : 0 = √501337 * 15 := by linarith
      simp  at this
    -- Whether $f(0) = 2004$ or not, the sum of  all of the values of x for which f(x)=2004
    -- are the same.
    by_cases hf0 : f 0 = 2004
    · have h4 : {x | f x = 2004} = {x | 3 * 2004 * x = 10 * x ^ 2 + 4 * x - 5} ∪ {0} := by
        ext x
        simp
        constructor <;> intro h
        · by_cases x0 : x = 0
          · simp [x0]
          · simp [x0]
            exact (h3 x x0).2 h
        · by_cases x0 : x = 0
          · simp [x0, hf0]
          · simp [x0] at h
            exact (h3 x x0).1 h
      rw [h4, finsum_mem_union]
      · rw [aux]
        simp
        rw [round_eq, Int.floor_eq_iff]
        norm_num
      · simp
      simp [hroots]
      simp
    · have h4 : {x | f x = 2004} = {x | 3 * 2004 * x = 10 * x ^ 2 + 4 * x - 5} := by
        ext x
        simp
        constructor <;> intro h
        · have : x ≠ 0 := fun x0 => hf0 (by rw [x0] at h; exact h)
          exact (h3 x this).2 h
        · have : x ≠ 0 := fun x0 => by simp [x0] at h
          exact (h3 x this).1 h
      rw [h4, aux, round_eq, Int.floor_eq_iff]
      norm_num
