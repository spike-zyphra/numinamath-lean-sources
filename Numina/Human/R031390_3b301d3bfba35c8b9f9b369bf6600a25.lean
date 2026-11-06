import Mathlib

open Real Set
open scoped BigOperators

/- 18. The even function $f(x)$ defined on $[-2,2]$ is monotonically decreasing on the interval $[0,2]$. If $f(1-m)<f(m)$, find the range of values for $m$.

 untranslated text remains unchanged. -/
theorem algebra_263198 {f : ℝ → ℝ} (hf : ∀ x ∈ (Icc (-2) 2), f x = f (-x)) (hfd : AntitoneOn f (Icc 0 2)) (hm : 1-m ∈ (Icc (-2) 2) ∧ m ∈ (Icc (-2) 2)) : (f (1 - m) < f m) → (-1 ≤ m ∧ m < 1 / 2) := by
  unfold AntitoneOn at hfd
  simp_all only [Set.mem_Icc]
  
  intro h
  -- -1 ≤ m as 1 - m ≤ 2
  constructor
  linarith
  by_contra bge1o2; push_neg at bge1o2
  -- We discuss two cases: m≥1 and m < 1. Both give m < 1/2.
  by_cases mge1 : 1≤ m
  have : f m ≤ f (m-1) := by 
    apply hfd
    constructor; linarith; linarith;
    constructor; linarith; linarith; linarith
  have : f (1-m) = f (m-1) := by 
    have : f (1 - m) = f (-(1 - m)) := by 
      apply hf (1-m)
      constructor; linarith; linarith;
    rw [this]; simp
  linarith

  have ml1 : m < 1 := by linarith
  have : 1-m ≤ m := by linarith
  have : f m ≤ f (1-m) := by 
    apply hfd
    constructor; linarith; linarith;
    constructor; linarith; linarith; linarith
  linarith


