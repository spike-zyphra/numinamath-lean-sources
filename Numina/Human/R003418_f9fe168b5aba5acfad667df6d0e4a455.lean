import Mathlib

/- Lemma 1: The set of solutions to x^2 - 3x + 2 = 0 is {1, 2}. -/
lemma lemma_1 : {x : ℝ | x ^ 2 - 3 * x + 2 = 0} = {1, 2} := by
  ext x
  simp
  rw [show x ^ 2 - 3 * x + 2 = (x - 1) * (x - 2) by ring]
  simp [sub_eq_zero]

/- Lemma 2: The set of solutions to x^2 + px + q = 0 is {r} if and only if p = -2r and q = r^2. -/
lemma lemma_2 {p q r : ℝ} :
    {x | x ^ 2 + p * x + q = 0} = {r} ↔ p = -2 * r ∧ q = r ^ 2 := by
  constructor
  . -- If the set of solutions is {r}
    rintro hx
    -- Then r is a solution to the equation
    have h₁ : r ^ 2 + p * r + q = 0 := by
      apply_fun (r ∈ ·) at hx
      simpa using hx
    -- And -p - r is also a solution by symmetry
    have h₂ : (-p - r) ^ 2 + p * (-p - r) + q = 0 := by
      linear_combination h₁
    -- So -p - r must be equal to r
    apply_fun (-p - r ∈ ·) at hx
    simp [h₂] at hx
    -- Therefore p = -2r
    obtain rfl : p = -2 * r := by linear_combination -hx
    -- And q = r^2
    simp
    linear_combination h₁
  . -- If p = -2r and q = r^2
    rintro ⟨rfl, rfl⟩
    ext x
    simp
    -- The equation x^2 + px + q = 0 is equivalent to (x - r)^2 = 0
    rw [show x ^ 2 + -(2 * r * x) + r ^ 2 = (x - r) ^ 2 by ring]
    simp [sub_eq_zero]

/- Example 2 Given $A=\left\{x \mid x^{2}+p x+q=0, x \in \mathrm{R}\right\}, B=\left\{x \mid x^{2}-3 x+2\right.$ $=0, x \in \mathrm{R}\}$, and $A \cap B=A$, find the values or relationship of $p$ and $q$. -/
theorem algebra_178646 :
    {(p, q) : ℝ × ℝ | let A := {x | x ^ 2 + p * x + q = 0}; let B := {x | x ^ 2 - 3 * x + 2 = 0}; A ∩ B = A} =
    {(p, q) : ℝ × ℝ | p ^ 2 < 4 * q} ∪ {(-2, 1), (-4, 4), (-3, 2)} := by
  -- Let's simplify the problem by using lemma 1, lemma 2, and the fact that A ∩ B = A if and only if A ⊆ B, also the fact that A ⊆ {x, y} if and only if A = ∅ or A = {x} or A = {y} or A = {x, y}
  ext ⟨p, q⟩
  simp [lemma_1, Set.subset_pair_iff_eq, lemma_2]
  norm_num
  -- It suffices to show that the set of solutions to x^2 + px + q = 0 is empty if and only if p^2 < 4q, and that the set of solutions to x^2 + px + q = 0 is {1, 2} if and only if p = -3 and q = 2
  suffices H : ({x | x ^ 2 + p * x + q = 0} = ∅ ↔ p ^ 2 < 4 * q) ∧ ({x | x ^ 2 + p * x + q = 0} = {1, 2} ↔ p = -3 ∧ q = 2) by itauto -- We use `itauto` to prove a logically trivial statement constructively
  constructor
  . -- We show that the set of solutions to x^2 + px + q = 0 is empty if and only if p^2 < 4q
    -- Let's prove the negation of both sides are equivalent
    rw [← not_iff_not]
    -- Simplify
    push_neg
    simp [Set.Nonempty]
    constructor
    . -- If there is some solution, then p^2 - 4q is non-negative
      rintro ⟨x, hx⟩
      -- Since we have (2x + p)^2 ≥ 0, and cancelling x gives p^2 - 4q ≥ 0
      have h := sq_nonneg (2 * x + p)
      linarith
    . -- If p^2 - 4q is non-negative, then there is some solution
      intro H
      -- The discriminant of the quadratic equation is non-negative, thus equals the square of its square root
      have h := exists_quadratic_eq_zero (a := 1) (b := p) (c := q)
      simp [discrim] at h
      replace H : 0 ≤ p ^ 2 - 4 * q := by linarith only [H]
      rcases h (√(p ^ 2 - 4 * q)) (by simp [H]) with ⟨x, hx⟩
      exact ⟨x, by linear_combination hx⟩
  . -- We show that the set of solutions to x^2 + px + q = 0 is {1, 2} if and only if p = -3 and q = 2
    constructor
    . -- If the set of solutions is {1, 2}, then 1 and 2 are solutions
      intro H
      have h₁ := congrArg (1 ∈ ·) H
      have h₂ := congrArg (2 ∈ ·) H
      simp at h₁ h₂
      -- We just solve the system of linear equations
      constructor
      . linear_combination h₂ - h₁
      . linear_combination 2 * h₁ - h₂
    . -- If p = -3 and q = 2, then the set of solutions is {1, 2}
      -- Let's use lemma 1.
      rintro ⟨rfl, rfl⟩
      convert lemma_1 using 4 with x
      ring