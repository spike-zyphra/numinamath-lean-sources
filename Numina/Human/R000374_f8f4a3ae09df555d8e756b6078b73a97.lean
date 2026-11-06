import Mathlib

/-Given $a\in R$, solve the inequality with respect to $x$: $ax^{2}-(a+3)x+3\leqslant 0$.-/
theorem algebra_9268_1 (a : ℝ) (ha : a < 0) :
{x | a * x ^ 2 - (a + 3) * x + 3 ≤ 0} = {x | x ≤ 3 / a ∨ 1 ≤ x} := by
-- Prove that $3/a$ is negative
  have : 3 / a < 0 := by
    rw [div_neg_iff]; left; constructor; simp; assumption
-- Simplify assumptions and break "iff"
  ext x; simp;
  rw [show a*x^2-(a+3)*x+3=(a*x-3)*(x-1) by ring]; constructor
-- Apply mul_nonpos_iff to get two inequalities on $x$
  · intro hx; rw [mul_nonpos_iff] at hx
    rcases hx with hx|hx
-- Prove by cases
    · left; rcases hx with ⟨hx,_⟩; simp at hx
      rw [← le_div_iff_of_neg'] at hx; assumption; assumption
    right; linarith
-- Prove the reversed implication by cases
  intro hx; cases hx; rename_i hx
  · rw [mul_nonpos_iff]; left; constructor
    · simp; rw [le_div_iff_of_neg'] at hx; assumption; assumption
    linarith
  rename_i hx; rw [mul_nonpos_iff]; right; constructor
  · simp;
    have : a * x < 0 := by
      rw [mul_neg_iff]; right; constructor; linarith; linarith
    linarith
  linarith

/-Given $a\in R$, solve the inequality with respect to $x$: $ax^{2}-(a+3)x+3\leqslant 0$.-/
theorem algebra_9268_2 (a : ℝ) (ha : a = 0) :
{x | a * x ^ 2 - (a + 3) * x + 3 ≤ 0} = {x | 1 ≤ x} := by simp [ha]


/-Given $a\in R$, solve the inequality with respect to $x$: $ax^{2}-(a+3)x+3\leqslant 0$.-/
theorem algebra_9268_3 (a : ℝ) (ha : 0 < a ∧ a < 3) :
{x | a * x ^ 2 - (a + 3) * x + 3 ≤ 0} = {x | 1 ≤ x ∧ x ≤ 3 / a} := by
-- Prove that $3/a$ is greater than $1$
  have : 1 < 3 / a  := by
    rw [lt_div_iff]; simp; linarith; linarith
-- Simplify assumptions
  ext x; simp; rw [show a*x^2-(a+3)*x+3=(a*x-3)*(x-1) by ring]
  rw [mul_nonpos_iff]; constructor
-- Break "iff" and prove by cases
  · intro hx; cases hx; rename_i hx
    rcases hx with ⟨hx1, hx2⟩; simp at hx1; simp at hx2
    rw [← div_le_iff₀'] at hx1; linarith; linarith
    rename_i hx; rcases hx with ⟨hx1, hx2⟩
    simp at hx1; simp at hx2; rw [le_div_iff₀']
    constructor; assumption; assumption; linarith
-- Prove the reversed implication by cases
  rintro ⟨hx1, hx2⟩; right; simp; rw [← le_div_iff₀']
  constructor; assumption; assumption; linarith

/-Given $a\in R$, solve the inequality with respect to $x$: $ax^{2}-(a+3)x+3\leqslant 0$.-/
theorem algebra_9268_4 (a : ℝ) (ha : a = 3) :
{x | a * x ^ 2 - (a + 3) * x + 3 ≤ 0} = {1} := by
-- Break "iff" and simplify assumptions
  ext x; simp; constructor
  · simp [ha]; intro hx
    rw [show 3 * x ^ 2 - (3 + 3) * x + 3 = 3 * (x - 1) ^ 2 by ring] at hx
    rw [mul_nonpos_iff] at hx; cases hx; rename_i hx; simp at hx
-- Apply pow_two_nonneg on $x-1$ to force $x-1$ to be $0$
    have := pow_two_nonneg (x-1)
    have h'x : x - 1 = 0 := by
      have : (x - 1) ^ 2 = 0 := by linarith
      rw [pow_eq_zero_iff] at this; assumption; norm_num
    linarith; linarith
-- Prove the reversed implication by plug in $x=1$
  intro hx; rw [hx]; simp

/-Given $a\in R$, solve the inequality with respect to $x$: $ax^{2}-(a+3)x+3\leqslant 0$.-/
theorem algebra_9268_5 (a : ℝ) (ha : 3 < a) :
{x | a * x ^ 2 - (a + 3) * x + 3 ≤ 0} = {x | 3 / a ≤ x ∧  x ≤ 1} := by
-- Prove that $3/a$ is less than $1$
  have : 3 / a < 1 := by
    rw [div_lt_iff]; simp; linarith; linarith
-- Simplify assumptions
  ext x; simp; rw [show a*x^2-(a+3)*x+3=(a*x-3)*(x-1) by ring]
  rw [mul_nonpos_iff]; constructor
-- Break "iff" and prove by cases
  · intro hx; cases hx; rename_i hx
    rcases hx with ⟨hx1, hx2⟩; simp at hx1; simp at hx2
    rw [div_le_iff₀']; constructor; assumption; assumption; linarith
    rename_i hx; simp at hx; rcases hx with ⟨hx1, hx2⟩
-- Prove that $a*x$ is greater than $3$ and derive a contradiction
    have : 3 < a * x := by
      rw [show (3:ℝ)=3*1 by simp]; apply mul_lt_mul
      assumption; assumption; norm_num; linarith
    linarith
-- Prove the reversed implication by cases
  rintro ⟨hx1, hx2⟩; left; simp; rw [← div_le_iff₀']
  constructor; assumption; assumption; linarith