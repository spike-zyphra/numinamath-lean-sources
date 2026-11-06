import Mathlib

open Real Set
open scoped BigOperators

/- Determine the range of the function $f(x)=\arcsin x+\arctan x$. -/
theorem algebra_9019 (f : ℝ → ℝ)  (hf : f = λ x => arcsin x + arctan x) :
   f '' (Icc (-1) 1) = {y | -3 * π / 4 ≤ y ∧ y ≤ 3 * π / 4} := by
    -- The function $y=\arcsin x$ is strictly increasing on $[-1,1]$,
    -- and $y=\arctan x$ is strictly increasing on $\mathbb{R}$.
    have h1 := Real.strictMonoOn_arcsin
    have h2 : StrictMonoOn arctan (Icc (-1) 1) :=
      StrictMonoOn.mono (strictMonoOn_univ.2 <| Real.arctan_strictMono ) (by simp)
    -- Therefore, $y=\arcsin x+\arctan x$ is strictly increasing on $[-1,1]$.
    have h3 : StrictMonoOn f (Icc (-1) 1) := by
      simp [hf]
      exact StrictMonoOn.add h1 h2
    -- Find the minimum value:
    -- When $x=-1$, we have $\arcsin(-1)=-\dfrac{\pi}{2}$ and $\arctan(-1)=-\dfrac{\pi}{4}$.
    -- Thus, the minimum value of $f(x)$ is $-\dfrac{\pi}{2}-\dfrac{\pi}{4}=-\dfrac{3\pi}{4}$.
    -- When $x=1$, we have $\arcsin(1)=\dfrac{\pi}{2}$ and $\arctan(1)=\dfrac{\pi}{4}$. Thus,
    -- the maximum value of $f(x)$ is $\dfrac{\pi}{2}+\dfrac{\pi}{4}=\dfrac{3\pi}{4}$.
    apply Set.eq_of_subset_of_subset
    · show f '' Icc (-1) 1 ⊆ Set.Icc (-3 * π / 4) (3 * π / 4)
      rw [show (-3 * π / 4) = f (-1) by simp [hf]; nlinarith,
        show 3 * π / 4 = f 1 by simp [hf]; nlinarith]
      apply MonotoneOn.image_Icc_subset
      exact StrictMonoOn.monotoneOn h3
    · -- Because f is continuous on Icc (-1) 1, so `Set.Icc (-3 * π / 4) (3 * π / 4) ⊆ f '' Icc (-1) 1`
      show Set.Icc (-3 * π / 4) (3 * π / 4) ⊆ f '' Icc (-1) 1
      rw [show (-3 * π / 4) = f (-1) by simp [hf]; nlinarith,
        show 3 * π / 4 = f 1 by simp [hf]; nlinarith]
      apply intermediate_value_Icc
      · simp
      · simp [hf]
        apply ContinuousOn.add
        exact Continuous.continuousOn Real.continuous_arcsin
        exact Continuous.continuousOn Real.continuous_arctan
