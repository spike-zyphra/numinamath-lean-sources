import Mathlib

-- Show that if w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 16, then maximum of the absolute values is at least 2
lemma l_key (w x y z : ℝ) (h : w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 16) :
    max (max |w| |x|) (max |y| |z|) ≥ 2 := by
  -- Use contradiction
  by_contra! lt_two
  -- Each variable's square is less than 4
  have : w ^ 2 < 4 := by
    have : |w| < |2| := by aesop
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sq_lt_sq]
    tauto
  have : x ^ 2 < 4 := by
    have : |x| < |2| := by aesop
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sq_lt_sq]
    tauto
  have : y ^ 2 < 4 := by
    have : |y| < |2| := by aesop
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sq_lt_sq]
    tauto
  have : z ^ 2 < 4 := by
    have : |z| < |2| := by aesop
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sq_lt_sq]
    tauto
  -- The sum of squares is less than 16, a contardiction
  linarith

/- ## Task 1.

Let $a, b, c,$ and $d$ be real numbers such that


$$

a^{2}+b^{2}+c^{2}+d^{2}=a b+b c+c d+d a+8

$$


Determine the smallest possible value of the largest number in the set $\{|a-b|,|b-c|,|c-d|,|d-a|\}$. -/
theorem algebra_252996 :
    IsLeast {x | ∃ a b c d : ℝ, x = max (max (|a - b|) (|b - c|)) (max (|c - d|) (|d - a|)) ∧
      a^2 + b^2 + c^2 + d^2 = a * b + b * c + c * d + d * a + 8} 2 := by
  constructor
  · -- Show that 2 is attained as a minimum by using the solution (2, 0, 2, 0)
    simp
    use 2
    use 0
    use 2
    use 0
    simp
    norm_num
  -- Show that 2 is a lower bound
  unfold lowerBounds
  simp
  intro x a b c d hx h
  subst x
  -- Rewrite the condition to a sum of squares
  have : (a - b) ^ 2 + (b - c) ^ 2 + (c - d) ^ 2 + (d - a) ^ 2 = 16 := by linarith
  -- Apply the key lemma
  exact l_key _ _ _ _ this