import Mathlib

theorem algebra_190538 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 2 + z ^ 2 = x ^ 3 + y ^ 3 + z ^ 3} := by
  set S := {(x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 2 + z ^ 2 = x ^ 3 + y ^ 3 + z ^ 3}
  have h1 : S.Infinite := by
    apply Set.infinite_of_injective_forall_mem (f := λ (k : ℕ) => (1 + 2 * (k : ℤ) ^ 2, (k : ℤ) * (1 + 2 * (k : ℤ) ^ 2), - (k : ℤ) * (1 + 2 * (k : ℤ) ^ 2)))
    · -- Show that the function f is injective
      intro k1 k2 h
      simp [Prod.ext_iff] at h
      all_goals omega
    · -- Show that all elements in the image of f are in S
      intro k
      have h2 : ∀ (n : ℕ), (1 + 2 * (↑n : ℤ) ^ 2, (↑n : ℤ) * (1 + 2 * (↑n : ℤ) ^ 2), - (↑n : ℤ) * (1 + 2 * (↑n : ℤ) ^ 2)) ∈ S := by 
        intro n
        simp [S]
        all_goals
          ring_nf at *
          <;> norm_num [pow_succ, pow_zero, mul_add, mul_assoc] at *
          <;> ring_nf at *
          <;> norm_num at *
          <;> try { nlinarith [sq_nonneg (n : ℤ), sq_nonneg ((n : ℤ) * (1 + 2 * (n : ℤ) ^ 2)), sq_nonneg ((-n : ℤ) * (1 + 2 * (n : ℤ) ^ 2))] }
          <;> try { nlinarith [sq_nonneg (n : ℤ), sq_nonneg ((n : ℤ) * (1 + 2 * (n : ℤ) ^ 2)), sq_nonneg ((-n : ℤ) * (1 + 2 * (n : ℤ) ^ 2))] }
          all_goals try { ring_nf <;> omega }
      specialize h2 k
      simpa using h2
  exact h1