import Mathlib

-- we show the pow_mod lemma for ℤ
lemma int.pow_mod (a b: ℤ) (n: ℕ): a ^ n % b = (a % b) ^ n % b := by
   induction' n with n ih
   .
    simp
   .
    rw [show a ^ (n + 1) = a * a ^ n by ring]
    rw [Int.mul_emod]
    rw [ih]
    rw [show (a % b) ^ (n + 1) = (a % b) * (a % b) ^ n by ring]
    set c:= a % b
    set d:= c ^ n
    rw [Int.mul_emod]
    simp
    symm
    apply Int.mul_emod

/-Theorem: Let $A$ be a natural number, $K$ be an even natural number,
and $M$ be a natural number greater than 1. Define $n = A^K$. If $A \pmod M = M-1$, show that $n \pmod M = 1$.-/

theorem number_theory_636589 (K: ℕ) (A M: ℤ) (h1: 1 < M) (h2: A % M = M - 1) (h3: Even K):
  (A ^ K) % M = 1 := by

  rw [even_iff_exists_two_mul] at h3
  obtain ⟨k, rfl⟩ := h3
  replace h2: A ^ 2 % M = 1 := by
    rw [show A ^ 2 = A * A by ring]
    rw [Int.mul_emod]
    simp [h2]
    rw [Int.mul_emod]
    suffices (M - 1) % M = (-1) % M by
      rw [this]
      rw [← Int.mul_emod]
      simp
      apply Int.emod_eq_of_lt
      norm_num
      omega
    rw [show M - 1 = M + (-1) by ring]
    rw [Int.add_emod]
    simp
  rw [pow_mul]
  rw [int.pow_mod (A ^ 2) M k]
  simp [h2]
  apply Int.emod_eq_of_lt
  norm_num
  omega