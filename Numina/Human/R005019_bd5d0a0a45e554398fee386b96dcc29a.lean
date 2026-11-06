import Mathlib
/- Find all monotonic functions $f: \mathbb{R} \rightarrow \mathbb{R}$ satisfying the condition: for every real number $x$ and every natural number $n$

$$
\left|\sum_{i=1}^{n} i\left(f(x+i+1)-f^{2}(x+i)\right)\right|<C
$$

where $C>0$ is independent of $x$ and $f^{2}(x)=f(f(x))$. -/
theorem algebra_605092 : {f : ℝ → ℝ | StrictMono f ∧ (∃ c : ℝ, c > 0 ∧ (∀ n : ℕ, ∀ x : ℝ, |∑ i in Finset.range n, (i + 1) * (f (x + i + 2) - f (f (x + i + 1)))| < c))} = {fun x => x + 1}:= by
  ext f
  constructor
  .
    -- Forward direction: if f satisfies the conditions, then f(x) = x + 1
    intro h
    simp at h
    rcases h with ⟨h1, ⟨c, hc, h2⟩⟩
    -- Show that |f(x+n+2) - f(f(x+n+1))| < 2c/(n+1) for all n and x
    have h4 : ∀ n : ℕ, ∀ x : ℝ, |f (x + n + 2) - f (f (x + n + 1))| < 2 * c / (n + 1):= by
      intro n x
      have g1:= h2 n x
      have g2:= h2 (n + 1) x
      -- Define sums for n and n+1 terms
      set a:= ∑ i ∈ Finset.range n, (↑i + 1) * (f (x + ↑i + 2) - f (f (x + ↑i + 1))) with ha
      set b:= ∑ i ∈ Finset.range (n + 1), (↑i + 1) * (f (x + ↑i + 2) - f (f (x + ↑i + 1))) with hb
      clear_value a b
      rw [Finset.sum_range_succ, ←ha] at hb
      have g3 : n + 1 > 0:= by omega
      rify at g3
      -- Use the fact that |b-a| ≤ |b| + |a| to bound the difference
      suffices |f (x + ↑n + 2) - f (f (x + ↑n + 1))| * (n + 1) < 2 * c by exact (lt_div_iff₀ g3).mpr this
      rw [show (↑n : ℝ) + 1 = |(↑n : ℝ) + 1| by exact Eq.symm (abs_of_pos g3)]
      rw [Eq.symm (abs_mul _ _)]
      rw [show (f (x + ↑n + 2) - f (f (x + ↑n + 1))) * (↑n + 1) = b - a by linarith]
      have g4 : |b - a| ≤ |b| + |a|:= by exact abs_sub b a
      linarith
    -- Transform the bound to show |f(x+1) - f(f(x))| < 2c/(n+1) for all n and x
    replace h4 : ∀ (n : ℕ) (x : ℝ), |f (x + 1) - f (f x)| < 2 * c / (↑n + 1):= by
      intro n x
      replace h4:= h4 n (x - n - 1)
      ring_nf at h4 ⊢
      exact h4
    -- Show that f(x+1) - f(f(x)) = 0 for all x by contradiction
    replace h4 : ∀ x : ℝ, f (x + 1) - f (f x) = 0:= by
      intro x
      by_contra H
      replace H : |f (x + 1) - f (f x)| > 0:= by positivity
      set t:= |f (x + 1) - f (f x)| with ht
      clear_value t
      -- Choose n large enough to get a contradiction
      replace h4:= h4 (⌊2 * c / t⌋.natAbs) x
      rw [←ht] at h4
      set b:= ⌊2 * c / t⌋.natAbs with hb
      clear_value b
      zify at hb
      have hbpos : b ≥ 0:= by
        zify
        rw [hb]
        positivity
      replace g : ⌊2 * c / t⌋ ≥ 0:= by positivity
      rw [abs_of_nonneg g] at hb
      replace hb : b + 1 = ⌊2 * c / t⌋ + 1:= by linarith
      rify at hb
      replace g : ↑⌊2 * c / t⌋ + (1 : ℝ) > 2 * c / t:= by exact Int.lt_floor_add_one (2 * c / t)
      rw [←hb] at g
      replace g : (b + 1) * t > 2 * c:= by exact (mul_inv_lt_iff₀ H).mp g
      replace g : (t : ℝ) > 2 * c / ((b : ℝ) + 1):= by
        replace hbpos : (↑b : ℝ) + 1 > 0:= by positivity
        exact (div_lt_iff₀' hbpos).mpr g
      linarith
    -- Prove that f(x) = x + 1 by contradiction
    simp
    funext x
    replace h4:= h4 x
    replace h4 : f (f x) = f (x + 1):= by linarith
    simp [StrictMono] at h1
    by_contra H
    replace H : f x < x + 1 ∨ f x > x + 1:= by exact lt_or_gt_of_ne H
    rcases H with H | H
    all_goals
      replace h1:= h1 H
      linarith
  .
    -- Backward direction: if f(x) = x + 1, then f satisfies the conditions
    intro h
    simp at h
    simp
    refine ⟨?_, ?_⟩
    .
      -- Show that f(x) = x + 1 is strictly monotonic
      simp [StrictMono]
      intro a b hab
      simp [h]
      exact hab
    .
      -- Show that f(x) = x + 1 satisfies the bounded sum condition with c = 1
      use 1
      simp
      intro n x
      simp [h]
      ring_nf
      simp
