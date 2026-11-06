import Mathlib

open Real

/-For $x>0$, let $f(x)=x^{x}$. Find all values of $x$ for which $f(x)=f^{\prime}(x)$.-/
theorem calculus_611206 (hf : ∀ (x : ℝ), 0 < x → f x = x ^ x) : ∀ x > 0, f x = deriv f x ↔ x = 1 := by
-- Rewrite hf to the following form
  replace hf : ∀ x ∈ Set.Ioi (0:ℝ), f x = exp (log x * x) := by
      intro x hx; simp at hx; rw [hf, exp_mul, exp_log]
      all_goals exact hx
-- Prove that $f$ is differentiable when $x>0$
  have df : DifferentiableOn ℝ f (Set.Ioi 0) := by
    rw [differentiableOn_congr hf]; intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.exp; apply DifferentiableAt.mul
    apply DifferentiableAt.log; any_goals exact differentiableAt_id'
    simp at hx; positivity
-- Define $g(x)$ to be $log f(x)$
  let g := fun x => log (f x)
  intro x hx; constructor
-- Compute the derivative of $g$ in two ways to get an identity about $f$ and the derivative of $f$
  · intro hfdf; have : deriv g x = 1 + log x := by
      rw [← derivWithin_of_isOpen (show IsOpen (Set.Ioi (0:ℝ)) by exact isOpen_Ioi)]
      dsimp [g]; have : Set.EqOn (fun x => log (f x)) (fun x => x * log x) (Set.Ioi 0) := by
        intro x hx; simp; rw [hf, log_exp]; ring; exact hx
      rw [derivWithin_congr this (by rw [hf, log_exp]; ring; simp; exact hx)]
      rw [derivWithin_of_isOpen (show IsOpen (Set.Ioi (0:ℝ)) by exact isOpen_Ioi)]
      rw [deriv_mul, deriv_id'', deriv_log, mul_inv_cancel₀]; simp; ring; positivity
      exact differentiableAt_id'; apply DifferentiableAt.log
      exact differentiableAt_id'; positivity
      all_goals simp; exact hx
  -- Use the assumption $f(x)=f'(x)$ to simplify the relation, we will get $x=1$
    dsimp [g] at this; rw [deriv.log, ← hfdf, div_self] at this
    simp at this; rcases this with _|_|_; any_goals linarith
  -- Finish the rest trivial goals
    any_goals rw [hf]; positivity; simp; exact hx
    apply df.differentiableAt; rw [mem_nhds_iff_exists_Ioo_subset]
    use x/2, 3*x/2; constructor
    · simp; constructor; exact hx
      rw [lt_div_iff₀']; linarith; norm_num
    simp [Set.subset_def]; intros; linarith
-- Conversely, if $x=1$, it is straightforward to check that $f(1)=f'(1)$
  intro xeq1; have : Set.EqOn f (fun x => exp (x * log x)) (Set.Ioi 0) := by
    intro x hx; simp; rw [hf, mul_comm]; exact hx
  rw [xeq1, hf, ← derivWithin_of_isOpen (show IsOpen (Set.Ioi (0:ℝ)) by exact isOpen_Ioi)]
  rw [derivWithin_congr this (by rw [hf, mul_comm]; simp)]
  rw [derivWithin_of_isOpen (show IsOpen (Set.Ioi (0:ℝ)) by exact isOpen_Ioi), _root_.deriv_exp]
  rw [deriv_mul, deriv_id'']; norm_num
  exact differentiableAt_id'; apply DifferentiableAt.log
  exact differentiableAt_id'; norm_num
  apply DifferentiableAt.mul; exact differentiableAt_id'
  apply DifferentiableAt.log; exact differentiableAt_id'; norm_num
  all_goals simp