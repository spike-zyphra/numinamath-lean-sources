import Mathlib

open Polynomial Finset

/- Let $P(x)$ be a polynomial with non-negative coefficients. Prove that if $P\left(\frac{1}{x}\right) P(x) \geq 1$ for $x=1$, then the same inequality holds for each positive $x$. -/
theorem inequalities_239340 {P : ℝ[X]} (hP : ∀ n, 0 ≤ P.coeff n)
    (h1 : 1 ≤ P.eval (1 / 1) * P.eval 1) :
    ∀ x > 0, 1 ≤ P.eval (1 / x) * P.eval x := by
-- Rewrite the evaluations of $P$ to summations in `h1` and the goal
  intro x xpos; repeat rw [eval_eq_sum_range] at *
  set n := P.natDegree with hn; clear_value n
  simp [← one_le_sq_iff_one_le_abs] at h1
-- Rewrite the product of summations to double summations, then split them at the diagonal
  rw [sum_mul_sum, ← sum_product'] at *
  rw [← sum_filter_not_add_sum_filter _ (fun p => p.1 = p.2)] at *
  simp_rw [ne_iff_lt_or_gt, filter_or] at *
  rw [sum_union] at *
-- Prove that $Prod.swap$ is a bijective between the upper diagonal and the lower diagonal
  have : image Prod.swap (filter (fun p => p.1 < p.2) (range (n + 1) ×ˢ range (n + 1))) =
  filter (fun p => p.1 > p.2) (range (n + 1) ×ˢ range (n + 1)) := by
    simp [Finset.ext_iff]
    intro i j; constructor
    · rintro ⟨_, _⟩; omega
    intro; use j, i; omega
-- Rearrange the terms to a $a + b ≤ c + d$-form
  rw [← this]; rw [← this] at h1
  rw [sum_image] at *; simp; simp at h1
  rw [← sum_add_distrib] at *; apply le_trans h1
-- Apply `add_le_add` to split the goal to two subgoals
  apply add_le_add
  -- The first goal simplifies to the nonnegativeness of a square
  · apply sum_le_sum; intro i hi
    simp at hi; rw [mul_mul_mul_comm]
    nth_rw 2 [mul_mul_mul_comm, mul_comm]
    rw [← mul_two]; nth_rw 7 [mul_comm]
    rw [← mul_add]; apply mul_le_mul_of_nonneg_left
    rw [← sub_nonneg]; field_simp
    apply div_nonneg; calc
      _ ≤ (x ^ i.2 - x ^ i.1) ^ 2 := by positivity
      _ = _ := by ring
    positivity; apply mul_nonneg
    all_goals apply hP
-- The second goal is actually an equality
  apply le_of_eq; apply sum_congr rfl
  intro i hi; simp at hi
  rw [mul_mul_mul_comm, hi.right, inv_mul_cancel₀]
  ring; positivity
-- Finish the rest trivial goals
  any_goals simp
  all_goals rw [disjoint_filter]; simp; omega