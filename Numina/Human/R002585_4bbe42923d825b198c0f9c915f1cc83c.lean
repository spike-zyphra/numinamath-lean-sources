import Mathlib

/-- For how many positive integers $n$ is $n^3 - 8n^2 + 20n - 13$ a prime number?
$\text{(A) one} \qquad \text{(B) two} \qquad \text{(C) three} \qquad \text{(D)
four} \qquad \text{(E) more than four}$ -/
theorem number_theory_1132 : {n : ℤ | 1 ≤ n ∧ Nat.Prime (n^3 - 8*n^2 + 20*n - 13).natAbs}.ncard = 3 := by

  -- Notice that the given expression factors as $(n - 1)(n^2 - 7n + 13)$.
  have (n : ℤ) : n^3 - 8*n^2 + 20*n - 13 = (n - 1) * (n^2 - 7*n + 13) := by ring
  have (n : ℤ) : (n^3 - 8*n^2 + 20*n - 13).natAbs = (n - 1).natAbs * (n^2 - 7*n + 13).natAbs := by
    rw [this, Int.natAbs_mul]
  have h1 {n : ℤ} : Nat.Prime (n^3 - 8*n^2 + 20*n - 13).natAbs ↔
      (Nat.Prime ((n - 1).natAbs * (n^2 - 7*n + 13).natAbs)) := by rw [this]

  -- Then if it is a prime, one of the factors must be $1$.
  have h2 {n : ℤ} : (Nat.Prime ((n - 1).natAbs * (n^2 - 7*n + 13).natAbs)) →
      (n - 1).natAbs = 1 ∨ (n^2 - 7*n + 13).natAbs = 1 := by
    rw [Nat.prime_mul_iff]
    rintro (⟨_, _⟩ | ⟨_, _⟩)
    · right; assumption
    · left; assumption

  -- The first factor is $1$ if and only if $n = 2$ or $n = 0$.
  have h3 {n : ℤ} : (n - 1).natAbs = 1 ↔ n = 2 ∨ n = 0 := by
    rw [Int.natAbs_eq_iff]
    simp
    constructor
    · rintro (h | h)
      · left; linarith
      · right; linarith
    · rintro (h | h) <;> subst h <;> norm_num

  -- The second factor is $1$ if and only if $n = 4$ or $n = 3$.
  have h4 {n : ℤ} : (n^2 - 7*n + 13).natAbs = 1 ↔ n = 4 ∨ n = 3 := by
    rw [Int.natAbs_eq_iff]
    simp
    constructor
    · rintro (h | h)
      · rw [←Int.sub_eq_zero (b := 4), ←Int.sub_eq_zero (b := 3), ←Int.mul_eq_zero]
        calc _ = n^2 - 7*n + 12 := by ring
             _ = (n^2 - 7*n + 13) - 1 := by ring
             _ = 1 - 1 := by rw [h]
              _ = 0 := by norm_num
      · exfalso
        suffices 1 * ((n : ℝ)*n) + (-7) * n + 14 ≠ 0 from ?_
        · contrapose! this
          simp
          norm_cast
          linarith
        · by_contra!
          rw [quadratic_eq_zero_iff_discrim_eq_sq, discrim] at this
          swap; norm_num
          norm_num at this
          suffices 0 ≤ ((2 * (n : ℝ) + -7) ^ 2) from ?_
          · contrapose! this with _h
            calc ((2 * (n : ℝ) + -7) ^ 2) = -7 := by rw [←this]
                 _ < 0 := by norm_num
          · apply zpow_two_nonneg
    · rintro (h | h) <;> subst h <;> norm_num

  -- Because $n$ is positive, we discard $n = 1$.
  have (n : ℤ) : (1 ≤ n) ∧ (Nat.Prime (n^3 - 8*n^2 + 20*n - 13).natAbs) ↔
      n = 2 ∨ n = 3 ∨ n = 4 := by
    rw [h1]
    constructor
    · rintro ⟨len, h⟩
      replace h := h2 h
      rw [h3, h4] at h
      aesop
    · rintro (h | h | h) <;> subst h <;> decide

  -- Therefore, the set we want is equal to $\{2, 3, 4\}$ which has $3$ elements.
  simp_rw [this]
  rw [Set.setOf_or, Set.setOf_or, Set.setOf_eq_eq_singleton]
  simp