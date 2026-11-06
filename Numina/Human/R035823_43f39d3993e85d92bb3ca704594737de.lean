import Mathlib

/- 10th Balkan 1993 Problem 1 Given reals a 1 ≤ a 2 ≤ a 3 ≤ a 4 ≤ a 5 ≤ a 6 satisfying a 1 + a 2 + a 3 + a 4 + a 5 + a 6 = 10 and (a 1 - 1) 2 + (a 2 - 1) 2 + (a 3 - 1) 2 + (a 4 - 1) 2 + (a 5 - 1) 2 + (a 6 - 1) 2 = 6, what is the largest possible a 6 ? Solution -/
theorem algebra_126836 :
    IsGreatest {x : ℝ | ∃ a : Fin 6 → ℝ, x = a 5 ∧
      (∀ i j, i < j → a i ≤ a j) ∧
      ∑ i, a i = 10 ∧ ∑ i, (a i - 1)^2 = 6} (3 + 1 / 3) := by
  simp only [IsGreatest, Fin.isValue, one_div, Set.mem_setOf_eq, upperBounds, forall_exists_index,
    and_imp]
  have hsum (f : Fin 6 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
    simp [Finset.sum_fin_eq_sum_range]
    simp [Finset.sum]
    ring
  constructor
  · let a : Fin 6 → ℝ := fun i => if i < 5 then 4 / 3 else 10 / 3
    -- show that there exists a sequence a(i) such that a(5) = 3 + 1 / 3
    -- and all other conditions are satisfied
    -- define a(i) = 4 / 3 for i < 5 and a(5) = 10 / 3 and show that
    -- all conditions are satisfied
    use a
    constructorm* _ ∧ _
    · simp [a]; norm_num
    · intro i j hij
      simp [a]
      split_ifs <;> norm_num
      omega
    · simp [hsum, a]
      norm_num
    · simp [hsum, a]
      norm_num
  · intro x a hx hmono
    -- suppose that a(i) satisfies all conditions and show that a(5) ≤ 3 + 1 / 3
    simp_rw [hsum]
    intro hs1 hs2
    -- from ∑ a(i) = 10 and ∑ (a(i) - 1)^2 = 6
    -- derive that ∑ (a(i) - 4/3)^2 = 4
    have eq : (a 0 - 4 / 3)^2 + (a 1 - 4 / 3)^2 + (a 2 - 4 / 3)^2
            + (a 3 - 4 / 3)^2 + (a 4 - 4 / 3)^2 + (a 5 - 4 / 3)^2 = 4 := by
      linear_combination -(2 / 3 * hs1) + hs2
    -- we get (a(5) - 4/3)^2 ≤ 4
    have ineq : (a 5 - 4 / 3)^2 ≤ 2^2 := by nlinarith
    -- so a(5) ≤ 2 + 4 / 3 = 3 + 1 / 3
    have := abs_le_of_sq_le_sq' ineq (by norm_num)
    linarith