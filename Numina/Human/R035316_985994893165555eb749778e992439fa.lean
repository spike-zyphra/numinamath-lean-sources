import Mathlib

/- A non-square rectangle has integer dimensions. The number  of square units in its area is triple the number of units in its perimeter. What is the smallest possible length for the perimeter? -/
theorem algebra_19551 : IsLeast {n : ℤ | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ a ≠ b ∧ a * b = 3 * (2 * (a + b)) ∧ n = 2 * (a + b)} 50 := by
  constructor
  · -- when $a = 10, b = 15$, the perimeter is $50$
    use 10
    use 15
    simp only [gt_iff_lt, Nat.ofNat_pos, ne_eq, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, not_false_eq_true, Int.reduceMul, Int.reduceAdd, true_and]
  -- $50$ is the least possible value for the perimeter
  intro n nin
  rcases nin with ⟨a, b, hapos, hbpos, aneb, abeq, neq⟩ 
  -- toward a contradiction, assume $n < 50$, then $a + b \leq 24$
  by_contra contra
  have le : a + b ≤ 24 := by
    linarith
  -- by $ab = 6(a + b)$, $a + b \geq 24$
  have eq : (a + b) * (a + b - 24) = (a - b) ^ 2 := by
      ring_nf
      rw [abeq]
      ring
  have ge : a + b ≥ 24 := by
    have ge : (a + b) * (a + b - 24) ≥ 0 := by
      rw [eq]
      exact sq_nonneg (a - b)
    have pos : 0 < a + b := by
      linarith
    apply (mul_nonneg_iff_right_nonneg_of_pos pos).mp at ge
    linarith
  -- so $a + b = 24$ and $a = b = 12$, a contradiction
  have eq2 : a + b = 24 := by
    linarith
  rw [eq2, sub_self, mul_zero] at eq
  have : a - b = 0 := by exact pow_eq_zero (id (Eq.symm eq))
  apply eq_of_sub_eq_zero at this
  contradiction