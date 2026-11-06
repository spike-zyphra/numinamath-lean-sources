import Mathlib

/- Let $A=(0,1),$ $B=(2,5),$ $C=(5,2),$ and $D=(7,0).$ A figure is created by connecting $A$ to $B,$ $B$ to $C,$ $C$ to $D,$ and $D$ to $A.$ The perimeter of $ABCD$ can be expressed in the form $a\sqrt2+b\sqrt{5}$ with $a$ and $b$ integers. What is the sum of $a$ and $b$?-/
theorem algebra_317 (A B C D : ℝ × ℝ) (hA : A = (0, 1)) (hB : B = (2, 5)) (hC : C = (5, 2)) (hD : D = (7, 0)) : ∃ a b : ℤ, (Real.sqrt ((dist A.1 B.1) ^ 2 + (dist A.2 B.2) ^ 2) + Real.sqrt ((dist B.1 C.1) ^ 2 + (dist B.2 C.2) ^ 2) + Real.sqrt ((dist C.1 D.1) ^ 2 + (dist C.2 D.2) ^ 2) + Real.sqrt ((dist D.1 A.1) ^ 2 + (dist D.2 A.2) ^ 2)) = a * Real.sqrt 2 + b * Real.sqrt 5 ∧ a + b = 12 := by
  -- substitute the given values
  rw [hA, hB, hC, hD]
  -- calculate the distances by dist x y = |x - y|
  simp [Real.dist_eq]
  -- simplify the expression
  norm_num
  -- prove that a = 10 and b = 2 is a solution
  
  have h : √20 + √18 + √8 + √50 = (10 : ℤ) * √2 + (2 : ℤ) * √5 ∧ (10 : ℤ) + (2 : ℤ) = (12 : ℤ) := by
    -- split the goal into two
    constructor
    . -- prove the first part by calculation
      calc √20 + √18 + √8 + √50 = √(2 * 2 * 5) + √(3 * 3 * 2) + √(2 * 2 * 2) + √(5 * 5 * 2) := by norm_num -- extend the square roots
        _ = √2 * √2 * √5 + √3 * √3 * √2 + √2 * √2 * √2 + √5 * √5 * √2 := by simp [Real.sqrt_mul] -- factor out the square roots
        _ = 2 * √5 + 3 * √2 + 2 * √2 + 5 * √2 := by rw [Real.mul_self_sqrt (by linarith), Real.mul_self_sqrt (by linarith), Real.mul_self_sqrt (by linarith)] -- combine the square roots
        _ = 10 * √2 + 2 * √5 := by ring -- combine the terms
    . -- trivially prove 10 + 2 = 12
      norm_num

  -- substitute the solution
  use 10, 2