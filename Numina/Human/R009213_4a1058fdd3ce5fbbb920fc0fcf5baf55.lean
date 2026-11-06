import Mathlib

open Real Finset

/- Let $a_{1}, a_{2}, \ldots, a_{n}$ be positive real numbers and $n \geq 1$. Show that

$$
\begin{aligned}
& n\left(\frac{1}{a_{1}}+\cdots+\frac{1}{a_{n}}\right) \\
& \quad \geq\left(\frac{1}{1+a_{1}}+\cdots+\frac{1}{1+a_{n}}\right)\left(n+\frac{1}{a_{1}}+\cdots+\frac{1}{a_{n}}\right)
\end{aligned}
$$

When does equality hold? -/
theorem inequalities_607967 {n : ℕ} (hn : 1 ≤ n) (a : ℕ → ℝ) (ha : ∀ i ∈ range n, 0 < a i) :
n * ∑ i ∈ range n, (1 / a i) ≥ (∑ i ∈ range n, (1 / (1 + a i))) * (n + ∑ i ∈ range n, (1 / a i)) ∧
(n * ∑ i ∈ range n, (1 / a i) = (∑ i ∈ range n, (1 / (1 + a i))) * (n + ∑ i ∈ range n, (1 / a i)) ↔
∀ i ∈ range n, ∀ j ∈ range n, a i = a j) := by
-- According to the reference answer, we define the following function $f$ and prepare to use Jensen's Inequality,
  let f : ℝ → ℝ := fun x => 1 / (1 / x + 1)
-- Compute the derivative of $f$
  have df : ∀ x > 0, deriv f x = 1 / (x + 1) ^ 2 := by
    intro x xpos; dsimp [f]; rw [deriv_div, deriv_const, zero_mul, one_mul]
    rw [deriv_add_const, deriv_div, deriv_const, zero_mul, zero_sub, zero_sub, one_mul]
    rw [deriv_id'']; simp; field_simp; ring; any_goals exact differentiableAt_const 1
    exact differentiableAt_id'; positivity
    rw [differentiableAt_add_const_iff]; apply DifferentiableAt.div; exact differentiableAt_const 1
    exact differentiableAt_id'; all_goals positivity
-- Compute the second derivative of $f$
  have d2f : ∀ x > 0, deriv^[2] f x = - 2 / (x + 1) ^ 3 := by
    intro x xpos; rw [Function.iterate_succ, Function.iterate_one, Function.comp]
    rw [← derivWithin_of_isOpen (show IsOpen (Set.Ioi (0:ℝ)) by exact isOpen_Ioi) (show x ∈ Set.Ioi 0 by simp; exact xpos)]
    have : Set.EqOn (deriv f) (fun x => 1 / (x + 1) ^ 2) (Set.Ioi 0) := by
      intro x hx; simp [← one_div]; simp at hx; apply df; exact hx
    rw [derivWithin_congr this, derivWithin_of_isOpen (show IsOpen (Set.Ioi (0:ℝ)) by exact isOpen_Ioi) (show x ∈ Set.Ioi 0 by simp; exact xpos)]
    rw [deriv_div, deriv_const, zero_mul, one_mul, zero_sub, deriv_pow'', deriv_add_const]
    rw [deriv_id'']; simp; field_simp; ring
    rw [differentiableAt_add_const_iff]; exact differentiableAt_id'; exact differentiableAt_const 1
    apply DifferentiableAt.pow; rw [differentiableAt_add_const_iff]; exact differentiableAt_id'
    positivity; exact df x xpos
-- Prove that $f$ is strictly concave when $x>0$
  have fcon : StrictConcaveOn ℝ (Set.Ioi 0) f := by
    apply strictConcaveOn_of_deriv2_neg'; exact convex_Ioi 0
    · intro x hx; simp at hx; apply ContinuousAt.continuousWithinAt; dsimp [f]
      apply ContinuousAt.div; exact continuousAt_const
      apply ContinuousAt.add; apply ContinuousAt.div; exact continuousAt_const; exact fun ⦃U⦄ a => a
      positivity; exact continuousAt_const; positivity
    intro x hx; simp at hx; simp [d2f x hx, neg_div]; positivity
-- Define a weight function $w$ to be the constant $1/n$ and a term function $p$ to be $1/a_i$
  let w : ℕ → ℝ := fun _ => 1 / n; have auxJI1 : ∀ i ∈ range n, 0 ≤ w i := by simp [w]
  let p : ℕ → ℝ := fun i => 1 / a i
  have auxJI2 : ∀ i ∈ range n, p i ∈ Set.Ioi 0 := by simp [p]; intros; apply ha; simp; assumption
-- Apply Jensen's Inequality to function $f$, weight $w$ and term $p$
  have JI := ConcaveOn.le_map_sum fcon.concaveOn auxJI1 (by simp [w]; field_simp) auxJI2
  dsimp [f, w, p] at JI; rw [← mul_sum, one_div_mul_eq_div, div_le_iff₀', mul_one_div] at JI
  constructor
  -- Manipulate the two sides of JI, then finish the first goal
  · rw [ge_iff_le, ← le_div_iff₀]; calc
      _ =  ∑ i ∈ range n, 1 / (1 / (1 / a i) + 1) := by
        apply sum_congr rfl; intros; field_simp; ring_nf
      _ ≤ _ := JI
      _ = _ := by
        rw [div_add_one, div_div_eq_mul_div, ← mul_sum, ← mul_assoc, mul_one_div_cancel]
        rw [one_mul, one_div_mul_eq_div, one_add_div, div_div_eq_mul_div, mul_comm]
        any_goals positivity
        suffices : 0 < ∑ i ∈ range n, 1 / n * (1 / a i); positivity
        apply sum_pos; intros; rw [div_mul_div_comm, one_mul, one_div_pos]
        apply mul_pos; positivity; apply ha; assumption
        use 0; simp; omega
    apply add_pos; positivity; apply sum_pos; intros; simp; apply ha; assumption
    use 0; simp; omega
-- To prove the condition when the equality holds, we apply StrictConcaveOn.map_sum_eq_iff to function $f$, weight $w$ and term $p$
  have auxJI3 : ∀ i ∈ range n, 0 < w i := by simp [w]; intros; omega
  have JIeq := StrictConcaveOn.map_sum_eq_iff fcon auxJI3 (by simp [w]; field_simp) auxJI2
-- Manipulate the two sides of JIeq, then finish the second goal
  dsimp [f, w, p] at JIeq; rw [← mul_sum, one_div_mul_eq_div, div_add_one] at JIeq
  rw [div_div_eq_mul_div, one_mul, one_add_div, div_div_div_cancel_right₀] at JIeq
  rw [div_eq_iff, ← mul_sum, mul_assoc, one_div_mul_eq_div, eq_div_iff, mul_comm] at JIeq
  simp_rw [one_div_one_div] at JIeq; simp_rw [add_comm]; rw [JIeq]; constructor
  · intro h i hi j hj; have hi' := h i hi; have hj' := h j hj
    apply eq_of_one_div_eq_one_div; rw [hi', hj']
  intro h t ht; rw [eq_div_iff]; calc
    _ = ∑ i ∈ range n, 1 / a t := by simp; ring
    _ = _ := by
      apply sum_congr rfl; intro x hx; suffices : a t = a x; rw [this]
      apply h; all_goals assumption
-- Finish the rest trivial goals
  any_goals positivity
  suffices : 0 < n + ∑ i ∈ range n, 1 / a i; positivity
  apply add_pos; positivity; apply sum_pos; intros; simp; apply ha; assumption
  use 0; simp; omega
  suffices : 0 < (∑ i ∈ range n, 1 / a i) / n; positivity
  apply div_pos; apply sum_pos; intros; simp; apply ha; assumption
  use 0; simp; omega; positivity