import Mathlib

/-Kostas and Helene have the following dialogue:

Kostas: I have in my mind three positive real numbers with product 1 and sum equal to the sum of all their pairwise products.

Helene: I think that I know the numbers you have in mind. They are all equal to 1.

Kostas: In fact, the numbers you mentioned satisfy my conditions, but I did not think of these numbers. The numbers you mentioned have the minimal sum between all possible solutions of the problem.

Can you decide if Kostas is right? (Explain your answer).-/
theorem algebra_604758 : IsLeast {s : ℝ | ∃ a b c : ℝ, s = a + b + c ∧ 0 < a ∧ 0 < b
    ∧ 0 < c ∧ a * b * c = 1 ∧ a + b + c = a * b + b * c + c * a} 3 := by
-- Split the goal to an existential goal and a lower bound goal
  simp [IsLeast, lowerBounds]; constructor
  -- Fulfill the existential goal with $a=b=c=1$, it is straightforward to check that they satisfy the desired properties
  · use 1, 1, 1; norm_num
-- To prove the lower bound of the set in question is $3$, we first show that one of $a$, $b$ and $c$ has to be $1$
  intro s a b c hs apos bpos cpos prd sm; simp [hs] at *
  have h : (a - 1) * (b - 1) * (c - 1) = 0 := by
    calc
      _ = (a * b * c - 1) + (a + b + c - a * b - b * c - c * a) := by ring
      _ = _ := by rw [prd, sm]; ring
-- Assume w. l. o. g. that $a$ is $1$
  wlog aeq : a = 1
  · by_cases hb : b = 1
    · specialize @this s b a c bpos apos cpos
      nth_rw 2 [add_comm]; apply this
      · rw [← prd]; ring
      · nth_rw 2 [add_comm]; rw [sm]; ring
      · exact hs
      · rw [← h]; ring
      exact hb
    specialize @this s c a b; rw [add_comm, ← add_assoc]
    apply this; any_goals assumption
    · rw [← prd]; ring
    · rw [add_assoc, add_comm, sm]; ring
    · rw [← h]; ring
    simp [or_assoc, sub_eq_zero] at h; rcases h with h|h|h
    any_goals contradiction
    exact h
-- Rewrite the sum of $a+b+c$ to $1+c+c⁻¹$, it is straighforward to see the latter is greater or equal to $3$ by completing a square
  simp [aeq] at *; rw [← eq_div_iff] at prd
  rw [← sub_nonneg, prd]; ring_nf; calc
    _ ≤ (√c - √c⁻¹) ^ 2 := by positivity
    _ = _ := by
      ring_nf; repeat rw [Real.sq_sqrt]
      rw [← Real.sqrt_mul, mul_inv_cancel₀, Real.sqrt_one]
      ring; all_goals positivity
  positivity