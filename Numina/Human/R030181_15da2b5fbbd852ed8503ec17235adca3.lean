import Mathlib

open Real Set
open scoped BigOperators

/- Given the function $f(x)=\sin x\cos x$, the smallest positive period of the function $f(x)$ is ______. -/
theorem algebra_9131 {f : ℝ → ℝ} (hf : f = λ x => sin x * cos x) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi) := by
  -- first we use the definition of smallest positive period
  unfold IsLeast; simp only [mem_setOf_eq]; constructor
  constructor
  -- of course $\pi$ is positive, which is trivial requirement of smallest positive period
  exact pi_pos
  -- then we prove that $\sin x\cos x=\sin (x+a)\cos (x+a)$ implies $a=\pi * k / 2$ where some $k$ is an integer.
  rw [hf]; simp only [sin_add_pi, cos_add_pi, mul_neg, neg_mul, neg_neg]
  unfold lowerBounds; simp only [mem_setOf_eq, and_imp]
  intro a a_pos e
  rw [hf] at e; simp only at e
  have : ∀ (x : ℝ), sin x * cos x = sin (x + a) * cos (x + a) := by
    by_contra p; push_neg at p
    have : (fun x => sin x * cos x) ≠ fun x => sin (x + a) * cos (x + a) := Function.ne_iff.mpr p
    contradiction
  -- by trig formula $\sin x\cos x=\sin (2 * x) / 2$, and we rearrange the quation in this way
  have : ∀ (x : ℝ), sin (2 * x) = sin (2 * (x + a)) := by intro x; rw [sin_two_mul x, sin_two_mul (x + a), mul_assoc, this x]; ring
  -- therefore, $2a$ is a period of $\sin x$.
  have period : ∀ (y : ℝ), sin y = sin (y + 2 * a) := by
    have : ∀ (x : ℝ), sin (2 * x) = sin (2 * x + 2 * a) := by
      intro x; have l: 2 * (x + a) = 2 * x + 2 * a := by ring
      rw [← l]; exact this x
    intro y; specialize this (y / 2)
    have k: 2 * (y / 2) = y := by ring
    rw [k] at this; exact this
  -- using special values $0$ and $\pi/2$, we can decide that $a = k\pi / 2$ for some integer $k$.
  have lina₁ : sin 0 = sin (0 + 2 * a) := period 0
  have lina₂ : sin (Real.pi / 2) = sin (Real.pi / 2 + 2 * a) := period (Real.pi / 2)
  simp only [sin_zero, zero_add] at lina₁; simp only [sin_pi_div_two] at lina₂
  have : sin (Real.pi / 2 + 2 * a) = sin (Real.pi / 2) * cos (2 * a) + cos (Real.pi / 2) * sin (2 * a) := by apply sin_add
  simp only [sin_pi_div_two, one_mul, cos_pi_div_two, zero_mul, add_zero] at this; rw [this] at lina₂
  have l₁ : sin (2 * a) = 0 := id (Eq.symm lina₁)
  have : ∃ k : ℤ, a = k * Real.pi / 2 := by
    apply Real.sin_eq_zero_iff.mp at l₁
    rcases l₁ with ⟨l₁₁, l₁₂⟩
    use l₁₁; rw [l₁₂]; ring
  rcases this with ⟨k, hyp⟩
  -- now if this integer $k<0$ then $a<0$, contradicting $a>0$ as it is positive period.
  by_cases h : k < 0
  have : a < 0 := by
    rw [hyp]; have pos₁ := pi_pos
    have : (k : ℝ) < 0 := Int.cast_lt_zero.mpr h
    have : (k : ℝ) * Real.pi < 0 := mul_neg_of_neg_of_pos this pos₁
    have : (2 : ℝ) > 0 := by norm_num
    linarith
  linarith
  -- as is the case of $k=0$, where $a=0$.
  by_cases h : k = 0
  rw [h] at hyp; simp only [Int.cast_zero, zero_mul, zero_div] at hyp
  linarith
  -- if $k=1$, then $\cos(2a) = -1$, contradiction with the initial conditions.
  by_cases h : k = 1
  rw [h] at hyp; simp only [Int.cast_one, one_mul] at hyp
  rw [hyp] at lina₂; absurd lina₂; ring_nf; norm_num
  -- therefore, $k$ must be greater then $2$, which implies $a\geqslant\pi$.
  have : 2 ≤ k := by omega
  have : (k : ℝ) * Real.pi ≥ 2 * Real.pi := by
    refine mul_le_mul_of_nonneg ?h₁ ?h₂ ?a0 ?d0 <;> norm_cast
    exact pi_nonneg
  linarith