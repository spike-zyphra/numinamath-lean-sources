import Mathlib

open Real

/-Determine all real numbers $x>1, y>1$, and $z>1$, satisfying the equation

$$
\begin{aligned}
x+y+z+\frac{3}{x-1} & +\frac{3}{y-1}+\frac{3}{z-1} \\
& =2(\sqrt{x+2}+\sqrt{y+2}+\sqrt{z+2})
\end{aligned}
$$-/
theorem algebra_607937 (x y z : ℝ) (gt1 : 1 < x ∧ 1 < y ∧ 1 < z) :
x + y + z + 3 / (x - 1) + 3 / (y - 1) + 3 / (z - 1) = 2 * (√(x + 2) + √(y + 2) + √(z + 2)) ↔
(x = (3 + √13) / 2 ∧ y = (3 + √13) / 2 ∧ z = (3 + √13) / 2) := by
-- Define $f$ to be the function $t + 3 / (t - 1) - 2 * √(t + 2)$
  let f : ℝ → ℝ := fun t => t + 3 / (t - 1) - 2 * √(t + 2)
-- Rewrite $f$ to a square form
  have feq : ∀ t > 1, f t = (t - 1 - √(t + 2)) ^ 2 / (t - 1) := by
    intro t ht; simp [f]; symm; rw [div_eq_iff, sub_mul, add_mul, div_mul_cancel₀, sub_sq]
    nth_rw 2 [pow_two]; rw [← sqrt_mul, sqrt_mul_self]; ring; any_goals linarith
-- Prove that $f$ is nonnegative
  have fge0 : ∀ t > 1, 0 ≤ f t := by
    intro t ht; rw [feq]; apply div_nonneg; positivity; any_goals linarith
-- Compute the discriminant of the quadratic equation $t^2-3*t-1=0$ for later use
  have disc : discrim (1:ℝ) (-3) (-1) = √13 * √13 := by
    rw [discrim, ← sqrt_mul, sqrt_mul_self]; ring; any_goals simp
  constructor
  · intro heq; rw [← sub_eq_zero] at heq
  -- Rewrite the equation to $f(x)+f(y)+f(z)=0$ and apply fge0 to $x$, $y$ and $z$
    replace heq : f x + f y + f z = 0 := by simp [f]; rw [← heq]; ring
    have := fge0 x gt1.left; have := fge0 y gt1.right.left; have := fge0 z gt1.right.right
    split_ands
    -- Solve for $x$ via quadratic roots formula quadratic_eq_zero_iff
    · have : f x = 0 := by linarith
      rw [feq] at this; simp at this; rcases this with h|_
      · rw [sub_eq_zero, ← pow_left_inj₀ _ _ (show 2≠0 by simp)] at h
        nth_rw 2 [pow_two] at h; rw [← sqrt_mul, sqrt_mul_self, ← sub_eq_zero] at h
        rw [show (x - 1) ^ 2 - (x + 2) = 1*(x*x)+(-3)*x+(-1) by ring] at h
        rw [quadratic_eq_zero_iff (show _ by simp) disc] at h; simp at h
        rcases h with _|h; assumption; suffices : x < 0; linarith
        rw [h]; apply div_neg_of_neg_of_pos; rw [sub_neg, ← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
        any_goals norm_num
        any_goals linarith
      any_goals linarith
    -- Solve for $y$ via quadratic roots formula quadratic_eq_zero_iff
    · have : f y = 0 := by linarith
      rw [feq] at this; simp at this; rcases this with h|_
      · rw [sub_eq_zero, ← pow_left_inj₀ _ _ (show 2≠0 by simp)] at h
        nth_rw 2 [pow_two] at h; rw [← sqrt_mul, sqrt_mul_self, ← sub_eq_zero] at h
        rw [show (y - 1) ^ 2 - (y + 2) = 1*(y*y)+(-3)*y+(-1) by ring] at h
        rw [quadratic_eq_zero_iff (show _ by simp) disc] at h; simp at h
        rcases h with _|h; assumption; suffices : y < 0; linarith
        rw [h]; apply div_neg_of_neg_of_pos; rw [sub_neg, ← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
        any_goals norm_num
        any_goals linarith
      any_goals linarith
  -- Solve for $z$ via quadratic roots formula quadratic_eq_zero_iff
    have : f z = 0 := by linarith
    rw [feq] at this; simp at this; rcases this with h|_
    · rw [sub_eq_zero, ← pow_left_inj₀ _ _ (show 2≠0 by simp)] at h
      nth_rw 2 [pow_two] at h; rw [← sqrt_mul, sqrt_mul_self, ← sub_eq_zero] at h
      rw [show (z - 1) ^ 2 - (z + 2) = 1*(z*z)+(-3)*z+(-1) by ring] at h
      rw [quadratic_eq_zero_iff (show _ by simp) disc] at h; simp at h
      rcases h with _|h; assumption; suffices : z < 0; linarith
      rw [h]; apply div_neg_of_neg_of_pos; rw [sub_neg, ← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      any_goals norm_num
      any_goals linarith
    any_goals linarith
-- Conversely, plug in $x=y=z=(3+√13)/2$ to check that indeed the equation holds
  rintro ⟨hx, hy, hz⟩; rw [← sub_eq_zero]; calc
    _ = f x + f y + f z := by simp [f]; ring
    _ = _ := by
      rw [hx, hy, hz, ← two_mul, ← add_one_mul]; simp; right; rw [feq]; simp
      left; rw [sub_eq_zero, ← pow_left_inj₀ _ _ (show 2≠0 by simp)]; nth_rw 2 [pow_two]
      rw [← sqrt_mul, sqrt_mul_self, ← sub_eq_zero]; ring_nf; norm_num; any_goals positivity
      rw [sub_nonneg, le_div_iff₀, ← sub_nonneg]; ring_nf; any_goals positivity
      rw [gt_iff_lt, lt_div_iff₀, ← sub_pos]; ring_nf; any_goals positivity