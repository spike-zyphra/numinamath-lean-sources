import Mathlib

/-Given the equation $\left(k-2\right)x^{2}-4x+4=0$ has two distinct real roots, the largest integer that $k$ can take is ______.-/
theorem algebra_9443_1 (k : ℝ) (h : ∃ x y, x ≠ y ∧ (k - 2) * x ^ 2 - 4 * x + 4 = 0 ∧ (k - 2) * y ^ 2 - 4 * y + 4 = 0) :
k ≤ 3 ∧ k ≠ 2 ∧ k ≠ 3 := by
-- Introduce two roots of the quadratic equation
  rcases h with ⟨x1, x2, h12, h1, h2⟩
-- Prove that $k$ can't be $2$ or $3$ by solving for $x1$ and $x2$
  have kne2 : k ≠ 2 := by
    intro h'; simp [h'] at h1 h2
    rw [← h1] at h2; simp at h2; symm at h2; contradiction
  have kne3 : k ≠ 3 := by
    intro h'; simp [h'] at h1 h2; ring_nf at h1 h2
    rw [show 4 - x1 * 4 + x1 ^ 2 = (2 - x1) ^ 2 by ring] at h1
    rw [show 4 - x2 * 4 + x2 ^ 2 = (2 - x2) ^ 2 by ring] at h2
    simp at h1 h2; simp [← h1] at h2; symm at h2; contradiction
-- Prove that the discriminant of the quadratic equation is nonnegative
-- by applying the key lemma quadratic_eq_zero_iff_discrim_eq_sq
  rw [pow_two, ← mul_assoc, sub_eq_add_neg, ← neg_mul, mul_assoc, quadratic_eq_zero_iff_discrim_eq_sq] at h1
  have discnonneg : 0 ≤ discrim (k - 2) (-4) 4 := by rw [h1]; apply pow_two_nonneg
-- Solve for bounds on $k$
  rw [discrim] at discnonneg; ring_nf at discnonneg; simp at discnonneg
  rw [show (48:ℝ)=3*16 by norm_num, mul_le_mul_right] at discnonneg
-- Prove our final goals
  norm_num; constructor; assumption
  constructor; assumption; assumption; norm_num
  rw [sub_ne_zero]; assumption

/-Given the equation $\left(k-2\right)x^{2}-4x+4=0$ has two distinct real roots, the largest integer that $k$ can take is ______.-/
theorem algebra_9443_2 : IsGreatest {m : ℤ | ∃ x y : ℝ, x ≠ y ∧
(m - 2) * x ^ 2 - 4 * x + 4 = 0 ∧ (m - 2) * y ^ 2 - 4 * y + 4 = 0} 1 := by
-- Rewrite the goal and prove it by applying algebra_9443_1
  rw [IsGreatest, upperBounds]; constructor
-- First check that when $m$ is $1$, the equation indeed has two distinct roots
  · simp; ring_nf; use 2*Real.sqrt 2-2; use -2*Real.sqrt 2-2
    constructor; intro h'; simp at h'
    rw [← neg_mul, mul_eq_mul_right_iff] at h'
    cases h'; linarith; rename_i h';
    rw [Real.sqrt_eq_zero] at h'; linarith; norm_num
-- After explicitly writing out the two solutions, we show that they satisfy the equation
    constructor
    · ring_nf; rw [pow_two, ← Real.sqrt_mul, Real.sqrt_mul_self]
      norm_num; norm_num; norm_num
    ring_nf; rw [pow_two, ← Real.sqrt_mul, Real.sqrt_mul_self]
    norm_num; norm_num; norm_num
-- Prove that $1$ is the largest integer $m$ can take by applying algebra_9443_1
  simp; intro a x1 x2 h12 h1 h2
  have aux1 : (a:ℝ) ≤ 3 ∧ (a:ℝ) ≠ 2 ∧ (a:ℝ) ≠ 3 → a ≤ 1 := by
    norm_cast; rintro ⟨h1, h2, h3⟩; by_contra h'; push_neg at h'
    interval_cases a; contradiction; contradiction
  apply aux1; apply (algebra_9443_1 a); use x1; use x2
