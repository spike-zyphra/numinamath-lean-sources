import Mathlib

/-
I have two cents and Bill has 
n
n cents. Bill wants to buy some pencils, which come in two different packages. One package of pencils costs 6 cents for 7 pencils, and the other package of pencils costs a dime for a dozen pencils (i.e. 10 cents for 12 pencils). Bill notes that he can spend all 
n
n of his cents on some combination of pencil packages to get 
P
P pencils. However, if I give my two cents to Bill, he then notes that he can instead spend all 
n
+
2
n+2 of his cents on some combination of pencil packages to get fewer than 
P
P pencils. What is the smallest value of 
n
n for which this is possible? Note: Both times Bill must spend all of his cents on pencil packages, i.e. have zero cents after either purchase. -/
theorem number_theory_609936 :
    (∃ a b c d : ℕ, 6 * a + 10 * b = 100 ∧ 6 * c + 10 * d = 100 + 2 ∧ 7 * a + 12 * b > 7 * c + 12 * d)
  ∧ (∀ n : ℕ, (∃ a b c d : ℕ, 6 * a + 10 * b = n ∧ 6 * c + 10 * d = n + 2 ∧ 7 * a + 12 * b > 7 * c + 12 * d) → n ≥ 100) := by
  constructor
  . -- (a,b,c,d) = (0,10,17,0) satisfies the conditions. We just need to check it.
    use 0
    use 10
    use 17
    use 0
    omega
  . -- Prove that 100 is the minimum solution. The system is linear and linarith closes the goal.
    intro n
    rintro ⟨ a, b, c, d, con1, con2, con3 ⟩
    linarith