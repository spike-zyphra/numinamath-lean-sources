import Mathlib

/-A point $(2, n)$ is 5 units away from the point $(-1, 1)$.
What is the product of all possible integer values for $n$?
Answer: -15. -/
theorem algebra_19894 (R : Finset ℤ) (hR : R = { n : ℤ | (2 - (-1)) ^ 2 + (n - 1) ^ 2 = 5 ^ 2 }) :
    R.prod id = -15 := by
  have : { n : ℤ | (2 - (-1)) ^ 2 + (n - 1) ^ 2 = 5 ^ 2 } = {5, -3} := by
    ext n
    constructor
    · -- Prove that {n : ℤ | (2 - (-1))^2 + (n - 1)^2 = 5^2} is a subset of {5, -3}
      intro hn
      rw [Set.mem_setOf_eq] at hn
      have : (n - 5) * (n + 3) = 0 := by linarith
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      obtain _ | _ := mul_eq_zero.mp this
      all_goals omega
    · -- Prove that {5, -3} is a subset of {n : ℤ | (2 - (-1))^2 + (n - 1)^2 = 5^2}
      rintro (hn | hn)
      all_goals rw [hn]; simp
  simp_all [this]
