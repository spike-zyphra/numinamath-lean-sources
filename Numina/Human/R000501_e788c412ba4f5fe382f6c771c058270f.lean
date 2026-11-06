import Mathlib

/-How many ordered pairs of real numbers $(x,y)$ satisfy the following system of equations? \[\left\{ \begin{aligned} x+3y&=3 \\ \left| |x| - |y| \right| &= 1 \end{aligned}\right.\]-/
theorem algebra_11479 : {(x, y) : ℝ × ℝ | x + 3 * y = 3 ∧ |(|x| -  |y|)| = 1}.ncard = 3 := by
-- Find the solution set by solving the equation in different cases
  have : {(x, y) : ℝ × ℝ | x + 3 * y = 3 ∧ |(|x| -  |y|)| = 1} = {(3/2,1/2),(0,1),(-3,2)} := by
    ext P; simp; constructor
    · rintro ⟨h1, h2⟩; rw [abs_eq] at h2; repeat rw [Prod.ext_iff]; simp
      rcases le_or_lt 0 P.1 with hx|hx <;> rcases le_or_lt 0 P.2 with hy|hy <;>
      rcases h2 with h2|h2
-- Case $P.1≥0$, $P.2≥0$ and $|P.1|-|P.2|=1$, simplify the absolute value and solve for $P.1$ and $P.2$
      · repeat rw [abs_of_nonneg] at h2
        apply_fun (fun t => t - 1) at h1; nth_rw 1 [← h2] at h1
        ring_nf at h1; apply_fun (fun t => t / 4) at h1
        norm_num at h1; rw [h1] at h2
        apply_fun (fun t => t + 1/2) at h2; norm_num at h2
        left; constructor; assumption; rw [← one_div]; any_goals assumption
-- Case $P.1≥0$, $P.2≥0$ and $|P.1|-|P.2|=-1$, simplify the absolute value and solve for $P.1$ and $P.2$
      · repeat rw [abs_of_nonneg] at h2
        apply_fun (fun t => t - -1) at h1; nth_rw 1 [← h2] at h1
        ring_nf at h1; apply_fun (fun t => t / 4) at h1
        norm_num at h1; rw [h1] at h2
        apply_fun (fun t => t + 1) at h2; norm_num at h2
        right; left; constructor; any_goals assumption
-- Case $P.1≥0$, $P.2<0$ and $|P.1|-|P.2|=1$, simplify the absolute value and solve for $P.2$
-- we will derive a contradiction in this case
      · rw [abs_of_nonneg, abs_of_neg] at h2
        apply_fun (fun t => t - 1) at h1; nth_rw 1 [← h2] at h1
        ring_nf at h1; apply_fun (fun t => t / 2) at h1
        norm_num at h1; linarith; any_goals assumption
-- Case $P.1≥0$, $P.2<0$ and $|P.1|-|P.2|=-1$, simplify the absolute value and solve for $P.2$
-- we will derive a contradiction in this case
      · rw [abs_of_nonneg, abs_of_neg] at h2
        apply_fun (fun t => t - -1) at h1; nth_rw 1 [← h2] at h1
        ring_nf at h1; apply_fun (fun t => t / 2) at h1
        norm_num at h1; linarith; any_goals assumption
-- Case $P.1<0$, $P.2≥0$ and $|P.1|-|P.2|=1$, simplify the absolute value and solve for $P.1$ and $P.2$     
      · rw [abs_of_neg, abs_of_nonneg] at h2
        apply_fun (fun t => t + 1) at h1; nth_rw 1 [← h2] at h1
        ring_nf at h1; apply_fun (fun t => t / 2) at h1
        norm_num at h1; rw [h1] at h2
        apply_fun (fun t => -t - 2) at h2; norm_num at h2
        right; right; constructor; any_goals assumption
-- Case $P.1<0$, $P.2≥0$ and $|P.1|-|P.2|=-1$, simplify the absolute value and solve for $P.1$
-- we will derive a contradiction in this case
      · rw [abs_of_neg, abs_of_nonneg] at h2
        apply_fun (fun t => t + -1) at h1; nth_rw 1 [← h2] at h1
        ring_nf at h1; apply_fun (fun t => t / 2) at h1
        norm_num at h1; rw [h1] at h2
        apply_fun (fun t => -t - 1) at h2; norm_num at h2
        linarith; any_goals assumption
-- Case $P.1<0$, $P.2<0$ and $|P.1|-|P.2|=1$, simplify the absolute value and solve for $P.2$
-- we will derive a contradiction in this case        
      · repeat rw [abs_of_neg] at h2
        apply_fun (fun t => t + 1) at h1; nth_rw 1 [← h2] at h1
        ring_nf at h1; apply_fun (fun t => t / 4) at h1
        norm_num at h1; linarith; any_goals assumption
-- Case $P.1<0$, $P.2<0$ and $|P.1|-|P.2|=-1$, simplify the absolute value and solve for $P.2$
-- we will derive a contradiction in this case 
      · repeat rw [abs_of_neg] at h2
        apply_fun (fun t => t + -1) at h1; nth_rw 1 [← h2] at h1
        ring_nf at h1; apply_fun (fun t => t / 4) at h1
        norm_num at h1; linarith; any_goals assumption
      norm_num
-- Conversely, check the given points are solutions to the system of equations
    intro hP; rcases hP with hP|hP|hP
    · rw [hP]; norm_num; repeat rw [abs_of_nonneg]
      any_goals norm_num; repeat rw [abs_of_nonneg]
      any_goals norm_num
    · rw [hP]; norm_num
    · rw [hP]; norm_num
-- Finish the final goal by applying the lemma
  rw [this]; norm_num