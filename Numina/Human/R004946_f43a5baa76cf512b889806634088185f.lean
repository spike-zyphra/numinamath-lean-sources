import Mathlib

/- The function $\mathrm{f}(\mathrm{n})$ is defined on the positive integers and takes non-negative integer values. It satisfies (1) $f(m n)=f(m)+f(n),(2) f(n)=0$ if the last digit of $n$ is 3 , (3) $f(10)=0$. Find $\mathrm{f}(1985)$. -/
theorem number_theory_604757 {f : ℕ → ℕ} (hpos : ∀ n, 0 < n → f n ≥ 0)
    (hmul : ∀ m n, f (m * n) = f m + f n) (hf : ∀ n, n % 10 = 3 → f n = 0)
    (hf' : f 10 = 0) : f 1985 = 0 := by 
    have h1 : ∀ (m n : ℕ), f (m * n) = 0 → f m = 0 ∧ f n = 0 := by
      --If $\mathrm{f}(\mathrm{mn})=0$,
      intro m n hmn
      --then $\mathrm{f}(\mathrm{m})+\mathrm{f}(\mathrm{n})=0$ (by $(1))$.
      rw [hmul] at hmn
      --But $\mathrm{f}(\mathrm{m})$ and $\mathrm{f}(\mathrm{n})$ are non-negative, so $\mathrm{f}(\mathrm{m})=\mathrm{f}(\mathrm{n})=0$.
      exact Nat.eq_zero_of_add_eq_zero hmn
    --Thus $f(10)=0$ implies $f(5)=0$.
    have h2 : f 5 = 0 := by
      obtain h3 := h1 5 2
      simp only [Nat.reduceMul, hf', forall_const] at h3
      exact h3.1
    --Similarly $f(3573)=0$ by (2),
    have h4 : f 3573 = 0 := by
      apply hf
      norm_num
    --so $f(397)=0$.
    have h5 : f 397 = 0 := by
      obtain h6 := h1 397 9
      simp only [Nat.reduceMul, h4, forall_const] at h6
      exact h6.1
    --Hence $f(1985)$ $=\mathrm{f}(5)+\mathrm{f}(397)=0$.
    have : 1985 = 5 * 397 := by norm_num
    rw [this, hmul, h2, h5]