import Mathlib

/-Given that $f(x)$ is an increasing function on $\mathbb{R}$, and for any $x \in \mathbb{R}$, it holds that $f\left[f(x)-3^x\right]=4$,
find the value of $f(\log_3 9)$.-/
theorem algebra_9385 {f : ℝ → ℝ} (hf : StrictMono f)
    (h : ∀ x, f (f x - 3 ^ x) = 4) :
    f (Real.logb 3 9) = 10 := by
  have hfc : ∃ m : ℝ , ∀ x, f x - 3 ^ x = m := by
    by_contra! hfc
    obtain ⟨x₁, _⟩ := hfc 1
    obtain ⟨x₂, hx₂⟩ := hfc (f x₁ - 3 ^ x₁)
    have eq :  f (f x₂ - 3 ^ x₂) = f (f x₁ - 3 ^ x₁) := by rw [h x₁, h x₂]
    absurd hx₂
    exact hf.injective eq
  -- Since $f(x)$ is an increasing function on $\mathbb{R}$, and 
  -- $f\left[f(x)-3^x\right]=4$ holds for any $x\in \mathbb{R}$,
  -- we deduce that $f(x)-3^x$ is a constant.
  obtain ⟨m, hfm⟩ := hfc
  -- Let's denote this constant as $m$, so $f(x) - 3^x = m$.
  replace h : f m = 4 := by rw [← hfm m, h m]
  replace hfm : ∀ x : ℝ, f x = m + 3 ^ x := by
    intro x
    rw [← sub_eq_iff_eq_add, hfm x]
  -- Consequently, this gives us $f(m) = 4$ and thus $f(x) = 3^x + m$.
  have : m = 1 := by
    let g : ℝ → ℝ := fun t ↦ t + 3 ^ t
    have hg : StrictMono g :=
    StrictMono.add strictMono_id (Real.strictMono_rpow_of_base_gt_one (by norm_num))
    have : g m = g 1 := by
      have geq1 : g m = 4 := by simp only [← hfm m, h, g]
      -- From the equation $f(m) = 4$, we have $3^m + m = 4$.
      have geq2 : g 1 = 4 := by norm_num
      rw [geq1, geq2]
      -- By inspection or trial-and-error, it can be determined that $m=1$ is the solution.
    exact hg.injective this
    -- Since the function $g(m) = 3^m + m$ is strictly increasing, we know there is a unique solution for $m$.
  subst this
  -- Thus, we have $f(x) = 3^x + 1$.
  rw [hfm]
  norm_num
  -- Now we can compute $f(\log_3 9)$:
  -- $$f(\log_3 9) = 3^{\log_3 9} + 1 = 9 + 1 = 10.$$
