import Mathlib

open Real Set
open scoped BigOperators

/- Determine the range of the function $y=x+\sin x$, where $x\in[0,2\pi]$.-/
theorem algebra_9216 (f : ℝ → ℝ) (hf : f = λ x => x + sin x) :
    f '' (Icc 0 (2 * π)) = Icc 0 (2 * π) := by
  have hf0 : f 0 = 0 := by simp [hf]
  have hf2pi : f (2 * π) = 2 * π := by simp [hf]
  apply le_antisymm
  -- Prove that the range of $f(x)$ is a subset of $[0, 2\pi]$.
  . intro y hy
    simp at hy ⊢
    -- Prove that $f(x)$ is monotone on $[0, 2\pi]$.
    have : MonotoneOn f (Icc 0 (2 * π)) := by
      apply monotoneOn_of_deriv_nonneg
      . exact convex_Icc 0 (2 * π)
      . rw [hf]
        apply ContinuousOn.add
        . exact continuousOn_id' (Icc 0 (2 * π))
        exact continuousOn_sin
      . intro x _
        rw [hf]
        apply DifferentiableWithinAt.add
        . simp
          apply differentiableWithinAt_id
        simp
        refine DifferentiableAt.differentiableWithinAt ?hf'.hg.h
        exact differentiableAt_sin
      intro x _
      rw [hf, deriv_add]
      simp
      have := cos_mem_Icc x
      simp at this
      linarith
      . exact differentiableAt_id'
      . exact differentiableAt_sin
    -- Since $f(x)$ is monotone on $[0, 2\pi]$, it's clear that $0\leq f(x)\leq 2\pi$.
    rcases hy with ⟨x, ⟨hx1, hx2⟩, hxy⟩
    rw [← hxy, ← hf0, ← hf2pi]
    constructor
    . exact this ⟨by linarith, by linarith⟩ ⟨hx1, hx2⟩ hx1
    exact this ⟨hx1, hx2⟩ ⟨by linarith, by linarith⟩ hx2
  -- Prove that $[0, 2\pi]$ is a subset of the range of $f(x)$.
  conv_lhs => rw [← hf0, ← hf2pi]
  -- This is easy by using the Intermediate Value Theorem.
  apply intermediate_value_Icc
  . positivity
  . rw [hf]
    apply ContinuousOn.add
    . exact continuousOn_id' (Icc 0 (2 * π))
    . exact continuousOn_sin
