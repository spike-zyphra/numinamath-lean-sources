import Mathlib

open Set

/- 11. (2001 Beijing College Entrance Examination) A function $f(x)$ defined on $D$ is said to be convex on $D$ if for any $x_{1}, x_{2} \in D$, it satisfies: $f\left(\frac{x_{1}+x_{2}}{2}\right) \geqslant \frac{1}{2}\left[f\left(x_{1}\right)+f\left(x_{2}\right)\right]$.

Given the quadratic function $f(x)=a x^{2}+x(a \in \mathbf{R}$, and $a \neq 0)$. (1) Prove that when $a<0$, the function $f(x)$ is convex on $\mathbf{R}$; (2) If $x \in[0,1]$, and $|f(x)| \leqslant 1$, find the range of values for $a$. -/
theorem algebra_128626 {a : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = a * x ^ 2 + x) :
    (a < 0 → ∀ x1 x2, f ((x1 + x2) / 2) ≥ (f x1 + f x2) / 2) ∧
    ((∀ x ∈ Icc 0 1, |f x| ≤ 1) ↔ a ∈ Ico (-2) 0) := by
  constructor
  -- prove that the function f is convex, i.e., f ((x + y) / 2) ≥ (f x + f y) / 2
  · intro ha x y
    simp_rw [hf, ge_iff_le]
    simp only [← sub_nonneg, sub_zero]
    -- simplify the inequality. We have to prove
    -- 0 ≤ a * x * y * (1 / 2) + a * x ^ 2 * (-1 / 4) + a * y ^ 2 * (-1 / 4)
    ring_nf
    -- 0 ≤ (1 / 4) * (-a) * (x - y) ^ 2 (since a < 0)
    --   = a * x * y * (1 / 2) + a * x ^ 2 * (-1 / 4) + a * y ^ 2 * (-1 / 4)
    calc
      0 ≤ (1 / 4) * (-a) * (x - y) ^ 2 := by
          apply mul_nonneg _ (sq_nonneg (x - y))
          exact mul_nonneg (by norm_num) (by linarith)
      _ = a * x * y * (1 / 2) + a * x ^ 2 * (-1 / 4) + a * y ^ 2 * (-1 / 4) := by ring
  -- now prove that |f x| ≤ 1 for x ∈ [0, 1] iff a ∈ [-2, 0)
  · simp only [mem_Icc, and_imp, mem_Ico, hf]
    constructor
    -- suppose that |f x| ≤ 1 and show that a ∈ [-2, 0)
    · intro h
      -- we have 1 ≥ |f 1| = |a + 1|
      specialize h 1 zero_le_one (le_refl 1)
      -- so -1 ≤ a + 1 ≤ 1
      simp [abs_le'] at h
      -- it follows that -2 ≤ a ≤ 0
      refine ⟨by linarith, ?_⟩
      -- a ≠ 0 implies that -2 ≤ a < 0
      exact lt_of_le_of_ne (by linarith) ha
    -- suppose that a ∈ [-2, 0) and show that |f x| ≤ 1 for x ∈ [0, 1]
    · intro ⟨ha2, ha0⟩ x hx0 hx1
      rw [abs_le']
      -- we have to prove that -1 ≤ x * (a * x + 1) ≤ 1 for x ∈ [0, 1] and a ∈ [-2, 0)
      -- these inequalities follow from
      -- 0 ≤ x ≤ 1 and -1 ≤ a * x + 1 ≤ 1
      constructor
      · nlinarith
      · nlinarith