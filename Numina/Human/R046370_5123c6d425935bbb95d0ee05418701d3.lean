import Mathlib

open Set Real

/- 5. Let $S=\left\{(x, y) \mid x^{2}-y^{2}=\right.$ odd, $\left.x, y \in \mathbf{R}\right\}, T=\left\{(x, y) \mid \sin \left(2 \pi x^{2}\right)-\sin \left(2 \pi y^{2}\right)=\right.$ $\left.\cos \left(2 \pi x^{2}\right)-\cos \left(2 \pi y^{2}\right), x, y \in \mathbf{R}\right\}$, then
A. $S \varsubsetneqq T$
B. $T \varsubsetneqq S$
C. $S=T$
D. $S \bigcap T=\varnothing$ -/
theorem algebra_271889 : {(x, y) : ℝ × ℝ | ∃ k:ℤ, (x ^ 2 - y ^ 2) = 2*k+1} 
⊂
{(x, y) : ℝ × ℝ | sin (2 * π * x ^ 2) - sin (2 * π *y ^ 2) =cos (2 * π * x ^ 2) - cos (2 * π * y ^ 2)} := by
  refine Set.ssubset_iff_subset_ne.mpr ?_
  constructor

  --We prove the containment by using the formula for sin a - sin b.
  intro (x,y)
  simp
  intro k
  intro h

  have t1: sin (2 * π * x ^ 2) - sin (2 * π * y ^ 2) = 2 * sin (π * x^2 - π * y^2) * cos (π * x^2 + π * y^2) := by
    have : sin (2 * π * x ^ 2) - sin (2 * π * y ^ 2) =
    2 * sin ((2 * π * x ^ 2 - 2 * π * y ^ 2) / 2) * cos ((2 * π * x ^ 2 + 2 * π * y ^ 2) / 2) := by 
      apply Real.sin_sub_sin (2 * π * x ^ 2) (2 * π * y ^ 2)
    rw [this]
    ring_nf

  have t2: cos (2 * π * x ^ 2) - cos (2 * π * y ^ 2) = -2 * sin (π * x^2 - π * y^2) * sin (π * x^2 + π * y^2) := by
    have : cos (2 * π * x ^ 2) - cos (2 * π * y ^ 2) =
    -2 * sin ((2 * π * x ^ 2 + 2 * π * y ^ 2) / 2) * sin ((2 * π * x ^ 2 - 2 * π * y ^ 2) / 2) := by 
      apply Real.cos_sub_cos (2 * π * x ^ 2) (2 * π * y^ 2)
    rw [this]
    ring_nf

  rw [t1,t2]
  have t3 : π * x ^ 2 - π * y ^ 2 = π * (x^2 - y^2) := by ring
  rw [t3]

  --Now, we have sin (π * (x^2 - y^2)) by the assumption on x^2 - y^2.
  have t4 : sin (π * (x^2 - y^2)) = 0 := by 
    rw [h]
    rw [Real.sin_eq_zero_iff]
    use 2 * k + 1
    norm_cast
    ring_nf
  rw [t4]
  ring

  -- It is not equal, as (0,0) is in the second set but not the first one.
  by_contra eq
  have c1: (0,0) ∈ {(x, y) | sin (2 * π * x ^ 2) - sin (2 * π * y ^ 2) = cos (2 * π * x ^ 2) - cos (2 * π * y ^ 2)} := by simp
  have c2: ¬((0:ℝ),0) ∈ {(x, y) | ∃ k: ℤ,(x^2-y^2)=2*k+1 }:= by
    by_contra eq
    simp at eq
    obtain ⟨k,hk⟩ := eq
    norm_cast at hk
    omega
  rw [←eq] at c1
  contradiction
  