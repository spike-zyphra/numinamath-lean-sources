import Mathlib

/- Let $\mathbb{R}$ denote the set of real numbers. Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that

$$
f\left(x^{2}\right)+f(x y)=f(x) f(y)+y f(x)+x f(x+y)
$$

for all $x, y \in \mathbb{R}$. -/
theorem algebra_606440 {f : ℝ → ℝ} : (∀ x y, f (x ^ 2) + f (x * y) = f x * f y + y * f x + x * f (x + y)) ↔
(∀ x, f x = -x) ∨ (∀ x, f x = 0) ∨ (∀ x, f x = 2 - x) := by
  constructor
  -- If $f(0)$ is not $0$, we can plug in $x=0$ to the functional equation to get $f(y)=2-y$
  · intro heq; by_cases f0 : f 0 ≠ 0
    · right; right; intro x; specialize heq 0 x; simp at heq
      ring_nf at heq; simp [← mul_add] at heq; rcases heq; simp_all; contradiction
  -- If $f(0)=0$, we first show $f(x^2)=x*f(x)$
    push_neg at f0; have fsq : ∀ x, f (x ^ 2) = x * f x := by
      intro x; specialize heq x 0; simp [f0] at heq; exact heq
  -- Show that $f$ is additive, i. e. $f(x+y)=f(x)+f(y)$
    have fadd : ∀ x y, x ≠ y → f (x + y) = f x + f y := by
      intro x y xney; have hxy := heq x y; have hyx := heq y x
      apply_fun fun t => t - (f (y ^ 2) + f (y * x)) at hxy; nth_rw 2 [hyx] at hxy
      rw [fsq, fsq] at hxy; ring_nf at hxy; apply_fun fun t => t + x * f y - f x * y at hxy
      ring_nf at hxy; rw [← mul_add, ← sub_mul, add_sub, ← sub_eq_add_neg, sub_sub] at hxy
      nth_rw 2 [mul_comm] at hxy; simp [← mul_add, ← sub_mul] at hxy
      rcases hxy; symm; assumption; rw [← sub_ne_zero] at xney; contradiction
    replace fadd : ∀ x y, f (x + y) = f x + f y := by
      intro x y; by_cases xney : x ≠ y; exact fadd x y xney
      push_neg at xney; rw [xney, ← two_mul, ← two_mul]
      by_cases hy : y = 0; simp [hy, f0]
      push_neg at hy; rw [show 2*y = y/3+(2*y/3+y) by ring, fadd, fadd, ← add_assoc, ← fadd]
      ring_nf; all_goals field_simp
      all_goals rw [← sub_eq_zero]; ring_nf; simp; assumption
  -- If there exists $r$ such that $f(r)$ is not $0$, show that $f(x)=-x$
    by_cases fne0 : ∃ r, f r ≠ 0
    · left; rcases fne0 with ⟨r, hr⟩; have rne0 : r ≠ 0 := by by_contra!; simp_all
      have f_or : ∀ x, f x = - x ∨ f x = 0 := by
        intro x; have hxx := heq x x; ring_nf at hxx; rw [fsq] at hxx; symm at hxx
        rw [mul_two, fadd, ← sub_eq_zero] at hxx; ring_nf at hxx
        simp [pow_two, ← add_mul] at hxx; rcases hxx
        · left; rw [← sub_eq_zero]; ring_nf; rw [add_comm]; assumption
        right; assumption
      intro x; by_cases xne0 : x = 0; simp [xne0, f0]
      rcases f_or x with _|fx; assumption
      specialize fadd x r; rcases f_or r with fr|_
      · rcases f_or (x+r) with hl|hr
        · rw [hl, fx, fr, ← sub_eq_zero] at fadd; ring_nf at fadd
          simp at fadd; contradiction
        simp [hr, fx] at fadd; symm at fadd; contradiction
      contradiction
  -- Otherwise $f$ is just constantly $0$
    push_neg at fne0; right; left; exact fne0
-- Conversely, it is straightforward to check that if $f$ is of the given form, it satisfies the functional equation in question
  intro h; rcases h with hf|hf|hf; all_goals intros; simp [hf]
  all_goals ring