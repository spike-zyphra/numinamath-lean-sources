import Mathlib

open Real Set
open scoped BigOperators

/-The minimum value of the function $f(x)=xe^{x}$ is ______.-/
theorem algebra_9239 (f : ℝ → ℝ) (hf : f = λ x => x * exp x) :
    IsLeast (range f) (-1 / exp 1) := by
  -- to solve the problem we use the definition of minimum
  unfold IsLeast; simp only [mem_range]
  have : rexp (-1) = (rexp 1)⁻¹ := by apply exp_neg 1
  -- we first varify the value is obtainable then solve the value by derivative analysis
  constructor
  -- notice that $-1/\exp1$ is equal to $f(-1)$
  use -1; rw [hf]; simp only [neg_mul, one_mul]
  rw [this]; ring
  -- to solve the value we wish to use the property of monotone functions
  unfold lowerBounds; simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    mem_setOf_eq]
  intro a
  have : f (-1) = -1 / exp 1 := by rw [hf]; simp only [neg_mul, one_mul]; rw [this]; ring
  rw [← this]
  -- to judge the monotonicity of the function we take its derivative
  have : deriv f = fun x => (x + 1) * exp x := by
    ext x; rw [hf, deriv_mul]; simp only [deriv_id'', one_mul, Real.deriv_exp]; ring
    exact differentiableAt_id'
    exact differentiableAt_exp
  -- because the function has non-negative derivative when $x≥-1$, we deduce it is monotone when $x≥-1$.
  have mono : MonotoneOn f {x | x ≥ -1} := by
    apply monotoneOn_of_deriv_nonneg
    exact Monotone.convex_ge (fun ⦃a b⦄ a => a) (-1)
    rw [hf]; refine Continuous.continuousOn ?hf.h
    refine Continuous.mul ?hf.h.hf ?hf.h.hg
    exact continuous_id'
    exact continuous_exp
    rw [hf]; refine DifferentiableOn.mul ?hf'.ha ?hf'.hb
    exact differentiableOn_id'
    refine Differentiable.differentiableOn ?hf'.hb.h
    exact differentiable_exp
    rw [this]; simp only [ge_iff_le]
    intro x h
    have : x + 1 ≥ 0 := by
      unfold interior at h
      simp only [mem_sUnion, mem_setOf_eq] at h
      rcases h with ⟨s, ⟨_, h₂⟩, h₃⟩
      have : x ∈ {x | -1 ≤ x} := h₂ h₃
      simp only [mem_setOf_eq] at this
      linarith
    have : rexp x > 0 := exp_pos x
    nlinarith
  -- with monotone property we are able to get $f(x)≥f(-1)$ as $x≥-1.$
  unfold MonotoneOn at this; simp only [ge_iff_le, mem_setOf_eq] at mono
  -- because the function has non-positive derivative when $x≤-1$, we deduce it is antitone when $x≤-1$.
  have anti : AntitoneOn f {x | x ≤ -1} := by
    apply antitoneOn_of_deriv_nonpos
    exact Monotone.convex_le (fun ⦃a b⦄ a => a) (-1)
    rw [hf]; refine Continuous.continuousOn ?hf.h
    rw [hf]; apply DifferentiableOn.mul
    exact differentiableOn_id'
    refine Differentiable.differentiableOn ?hf'.hb.h
    rw [this]; simp only [ge_iff_le]
    intro x h
    have : x + 1 ≤ 0 := by
      unfold interior at h
      simp only [mem_sUnion, mem_setOf_eq] at h
      rcases h with ⟨s, ⟨_, h₂⟩, h₃⟩
      have : x ∈ {x | x ≤ -1} := h₂ h₃
      simp only [mem_setOf_eq] at this
      linarith
    have : rexp x > 0 := exp_pos x
    nlinarith
  -- with antitone property we are able to get $f(x)≥f(-1)$ as $x≤-1.$
  unfold AntitoneOn at anti; simp only [mem_setOf_eq] at anti
  -- by discussing the two possible relationships between $-1$ and $a$ the desired result follows.
  by_cases hyp : a ≤ -1
  have : (-1 : ℝ) ≤ -1 := by norm_num
  specialize anti hyp this; exact anti hyp
  push_neg at hyp; have hyp : -1 ≤ a := le_of_lt hyp
  have : (-1 : ℝ) ≥ -1 := by norm_num
  specialize mono this hyp; exact mono hyp