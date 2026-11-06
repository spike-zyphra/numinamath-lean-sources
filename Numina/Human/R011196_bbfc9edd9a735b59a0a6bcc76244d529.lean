import Mathlib

open Real

/- ## Problem 1

a. Prove that for any real numbers $a, b, c, x, y, z$ the following inequality holds:


$$

(a x+b y+c z)^{2} \leq\left(a^{2}+b^{2}+c^{2}\right)\left(x^{2}+y^{2}+z^{2}\right)

$$


b. Determine the real numbers $x, y, z$ that satisfy the equality:

$3 \sqrt{2 y+z-2}+2 \sqrt{10-y-z}-\sqrt{x-y-z+2}+\sqrt{4-x+z}=14+\sqrt{z+y-x-2}$. -/

theorem inequalities_104785:
    (∀ a b c x y z : ℝ,
     (a * x + b * y + c * z) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2)) ∧
    (∀ (x y z: ℝ) (H1: 0 ≤ 2 * y + z - 2) (H2: 0 ≤ 10 - y - z)
     (H3: 0 ≤ x - y - z + 2) (H4: 0 ≤ 4 - x + z) (H5: 0 ≤ z + y - x - 2),
      3 * √(2 * y + z - 2) + 2 * √ (10 - y - z) - √ (x - y - z + 2) +
      √(4 - x + z)  = 14 + √(z + y - x - 2) ↔
      x = 4 ∧ y = 5 ∧ z = 1) := by

  -- equality that makes Lagrange inequality to work
  have lagrange_ineq_aux (a b c x y z: ℝ):
    (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) - (a * x + b * y + c * z) ^ 2 =
    (a * y - x * b) ^ 2 + (a * z - x * c) ^ 2 + (b * z - y * c) ^ 2 := by ring

  -- Lagrange inequality for n = 3
  have lagrange_ineq (a b c x y z: ℝ):
      (a * x + b * y + c * z) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2) := by
    -- few rewrites to get sum of squares that must be nonnegative in the goal
    rw [<- sub_nonneg, lagrange_ineq_aux]
    -- `nlinarith` solves this goal perfectly
    nlinarith

  -- let's destruct conjunction in the goal
  constructor
  . -- this is exactly `lagrange_ineq`
    exact lagrange_ineq
  . intros x y z H1 H2 H3 H4 H5
    constructor <;> intro H
    . -- direction left-to-right of double implication
      -- from all these inequalities such equality follows
      have H1: z = x - y + 2 := by linarith
      -- rewrite using `H1` and simplify
      rw [H1] at H; ring_nf at H; norm_num at H
      -- use `langrange_ineq` with specific values
      have H2 := lagrange_ineq_aux √(y + x) √(8 - x) √(6 - y) 3 2 1
      -- simplify all squared square roots in `H2`
      rw [sq_sqrt (by linarith)] at H2 H2 H2
      -- helpful equality to use
      have H3: (y + x + (8 - x) + (6 - y)) * (3 ^ 2 + 2 ^ 2 + 1 ^ 2) = 14 ^ 2 := by
        ring_nf
      -- simplify H2
      rw [H3] at H2; norm_num at H2; rw [H] at H2; norm_num at H2
      -- the left side of `H2` is zero and right side is
      -- sum of three squared values,
      -- therefore each of these summands (squares) are zero
      have H4: (√(y + x) * 2 - 3 * √(8 - x))^2 = 0 := by nlinarith
      have H5: (√(y + x) - 3 * √(6 - y))^2 = 0 := by nlinarith
      have H6: (√(8 - x) - 2 * √(6 - y))^2 = 0 := by nlinarith
      -- if square of number is zero, then the number is zero too
      -- simplifying `H4`, `H5`, `H6`
      simp only [pow_eq_zero_iff (n := 2) (by linarith)] at H4 H5 H6
      -- `H4`, `H5` and `H6` is basically a simple system of linear equations
      -- let's use linarith to prove values of each square root
      have H7: √(y + x) = 3 := by linarith
      have H8: √(8 - x) = 2 := by linarith
      have H9: √(6 - y) = 1 := by linarith
      -- id square root is equal to positive number,
      -- then we square both sides of such equality
      rw [sqrt_eq_cases] at H7 H8 H9
      norm_num at H7 H8 H9
      -- now `H7`, `H8`, `H9` makes a simple system of linear equation
      -- we can use `linarith` to prove each equality of goal
      refine ⟨by linarith, by linarith, by linarith⟩
    . -- direction right-to-left of double implication
      -- obtain values of `x`, `y`, `z` and substitute them everywhere
      obtain ⟨Hx, Hy, Hz⟩ := H
      subst x y z
      -- simplify goal using `norm_num`
      norm_num
      -- we must make two hints for `norm_num`, as it doesn't calculate square roots
      have H1: (9: ℝ) = 3 ^ 2 := by norm_num
      have H2: (4: ℝ) = 2 ^ 2 := by norm_num
      -- rewrite using `H1` and `H2`, then simplify
      rw [H1, H2]; simp only [Nat.ofNat_nonneg, sqrt_sq]; norm_num