import Mathlib

open BigOperators Complex Filter Finset Real TopologicalSpace Topology

theorem calculus_2156
  (f : ℝ → ℝ)
  (hf1 : Function.Bijective f)
  (hf2 : ∀ x, f x ≥ 0) :
  Set.Infinite {x | ¬ ContinuousAt f x} := by
  -- get a contradiction from the hf1
  -- indeed, the hf1 tells that f is a surjectivity
  -- we can get a contradiction from the fact
  -- that $f$ is not surjective.
  have h3 : Function.Surjective f := hf1.surjective
  -- Let's pick a real number $-1$ from $\mathbb{R}$.
  have h1 := h3 (-1 : ℝ)
  rcases h1 with ⟨x, hx⟩
  -- We have $f x = -1$, but $f x \geq 0$
  -- We get a contradiction.
  have hx0 : f x ≥ 0 := hf2 x
  linarith