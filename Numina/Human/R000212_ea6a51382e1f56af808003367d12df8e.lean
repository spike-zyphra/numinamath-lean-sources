import Mathlib

/-Let  $a,b$  be positive integers such that  $a+b^3$  is divisible by  $a^2+3ab+3b^2-1$ . Prove that  $a^2+3ab+3b^2-1$  is divisible by the cube of an integer greater than 1.-/
theorem number_theory_8583 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
(hab : (a ^ 2 + 3 * a * b + 3 * b ^ 2 - 1) ∣ (a + b ^ 3)) :
∃ c : ℕ, 1 < c ∧ c ^ 3 ∣ (a ^ 2 + 3 * a * b + 3 * b ^ 2 - 1) := by
-- Prove by contradiction, assume that for any integer $c$ greater that $1$, $c^3$ does not divide $a^2+3ab+3b^2-1$
  by_contra h'; push_neg at h'
-- Simplify the notations by naming a new variable $l$, then rewrite assumptions
  let l := a ^ 2 + 3 * a * b + 3 * b ^ 2 - 1
  have h'l0 : 1 ≤ l := by
    have : 1 ≤ a ^ 2 := by apply Nat.one_le_pow; assumption
    have : 1 ≤ b ^ 2 := by apply Nat.one_le_pow; assumption
    omega
  have hl0 : l ∣ a + b ^ 3 := by simp [l]; assumption
  have hl1 : l ∣ (a + b) ^ 3 := by
    have : (a + b) ^ 3 = a + b ^ 3 + a * (a ^ 2 + 3 * a * b + 3 * b ^ 2 - 1) := by
      rw [Nat.mul_sub, mul_one, ← Nat.add_sub_assoc]; nth_rw 3 [add_comm]; nth_rw 2 [add_comm]
      rw [← add_assoc]; simp; ring; apply Nat.le_mul_of_pos_right
      by_contra h'; simp at h'; linarith
    rw [this]; apply Nat.dvd_add; assumption; simp [l]

-- Prove that the powers occur in the prime factorization of $l$ are less or equal to $2$
  have hl2 : ∀ q, q ∈ l.primeFactors → padicValNat q l ≤ 2 := by
    intro q hq
    simp at hq
    rcases hq with ⟨hq1, _, _⟩
    by_contra h'q
    push_neg at h'q
    rw [Nat.lt_iff_add_one_le] at h'q
    simp at h'q; rcases Nat.prime_def_lt.mp hq1 with ⟨hq3, _⟩
    have : Fact (q.Prime) := by rw [fact_iff]; assumption
    have : q ^ 3 ∣ l := by rw [padicValNat_dvd_iff]; right; assumption
    have : ¬ q ^ 3 ∣ l := by simp [l]; apply h'; linarith
    contradiction

-- Prove that $l$ divides $(a+b)^2$ by comparing their prime factorizations
  have hl3 : l ∣ (a + b) ^ 2 := by
    rw [← Nat.factorization_le_iff_dvd, Finsupp.le_iff]; simp
    intro q hq1 hq2 hq3; rw [Nat.factorization_def, Nat.factorization_def]
    have : padicValNat q l ≤ 2 := by apply hl2; simp; exact ⟨hq1,hq2,hq3⟩
    have : 1 ≤ padicValNat q (a + b) := by
      have : Fact q.Prime := by rw [fact_iff]; assumption
      rw [Nat.one_le_iff_ne_zero, ← dvd_iff_padicValNat_ne_zero]
      rw [← Prime.dvd_pow_iff_dvd (Nat.prime_iff.mp hq1) (show 3≠0 by norm_num)]
      exact Nat.dvd_trans hq2 hl1; linarith
    linarith; assumption; assumption; norm_num; linarith
    by_contra hne; simp at hne; linarith

-- Derive a contradiction from the fact that $l$ has to be less or equal to $(a+b)^2$
  apply Nat.le_of_dvd at hl3; simp [l] at hl3
  nlinarith
  nlinarith
