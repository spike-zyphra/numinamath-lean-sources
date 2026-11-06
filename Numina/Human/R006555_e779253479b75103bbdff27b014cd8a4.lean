import Mathlib

/- Let $p_1, p_2, p_3, p_4$ be four distinct prime numbers. Let $N$ be their product, i.e., $N = p_1 \cdot p_2 \cdot p_3 \cdot p_4$.
Show that the exponent of $p_1$ in the prime factorization of $N$ is 1, the exponent of $p_2$ in the prime factorization of $N$ is 1, the exponent of $p_3$ in the prime factorization of $N$ is 1, and the exponent of $p_4$ in the prime factorization of $N$ is 1. Furthermore, show that for any prime number $q$ such that $q \neq p_1$, $q \neq p_2$, $q \neq p_3$, and $q \neq p_4$, the exponent of $q$ in the prime factorization of $N$ is 0. -/
theorem number_theory_638449 (p1 p2 p3 p4 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hp3 : p3.Prime) (hp4 : p4.Prime) (hpi : p1 ≠ p2 ∧ p1 ≠ p3 ∧ p1 ≠ p4 ∧ p2 ≠ p3 ∧ p2 ≠ p4 ∧ p3 ≠ p4)
    (N : ℕ) (hN : N = p1 * p2 * p3 * p4)
    : Nat.factorization N p1 = 1
    ∧ Nat.factorization N p2 = 1
    ∧ Nat.factorization N p3 = 1
    ∧ Nat.factorization N p4 = 1
    ∧
    ∀ q, q.Prime → q ≠ p1 → q ≠ p2 → q ≠ p3 → q ≠ p4 → Nat.factorization N q = 0 :=
by

  have : N.primeFactorsList.Perm [p1, p2, p3, p4] := by
    rw [hN]
    refine List.Perm.symm (Nat.primeFactorsList_unique ?_ ?_)
    . simp
      linarith
    . intro p ph
      simp at ph
      rcases ph with (h|h|h|h)
      <;> subst h <;> assumption

  have H := (@Nat.squarefree_iff_nodup_primeFactorsList N ?_).mpr
  have nodup : N.primeFactorsList.Nodup := by
    apply List.Nodup.perm (l := [p1, p2, p3, p4])
    . simp
      tauto
    . symm
      assumption
  rw [hN] at H nodup

  constructor
  . rw [hN]
    refine Nat.factorization_eq_one_of_squarefree ?_ hp1 ?_
    . apply H
      assumption
    . repeat rw [mul_assoc]
      apply Nat.dvd_mul_right
  constructor
  . rw [hN]
    refine Nat.factorization_eq_one_of_squarefree ?_ hp2 ?_
    . apply H
      assumption
    . rw [show p1 * p2 * p3 * p4 = p2 * (p1 * p3 * p4) by linarith]
      apply Nat.dvd_mul_right
  constructor
  . rw [hN]
    refine Nat.factorization_eq_one_of_squarefree ?_ hp3 ?_
    . apply H
      assumption
    . rw [show p1 * p2 * p3 * p4 = p3 * (p1 * p2 * p4) by linarith]
      apply Nat.dvd_mul_right
  constructor
  . rw [hN]
    refine Nat.factorization_eq_one_of_squarefree ?_ hp4 ?_
    . apply H
      assumption
    . rw [show p1 * p2 * p3 * p4 = p4 * (p1 * p2 * p3) by linarith]
      apply Nat.dvd_mul_right
  intro q hq ne1 ne2 ne3 ne4
  have : q ∉ N.primeFactorsList := by
    intro H
    have : q ∈ [p1, p2, p3, p4] := (List.Perm.mem_iff this).mp H
    simp at this
    rcases this with (_|_|_|_)
    all_goals tauto
  simp [Nat.factorization]
  intro _
  right; right
  intro H'
  apply this
  apply (Nat.mem_primeFactorsList_iff_dvd ?_ ?_).mpr
  assumption
  rw [hN]
  exact Squarefree.ne_zero (H nodup)
  assumption
  rw [hN]
  apply Nat.mul_ne_zero_iff.mpr
  constructor
  apply Nat.mul_ne_zero_iff.mpr
  constructor
  apply Nat.mul_ne_zero_iff.mpr
  constructor
  all_goals
     apply Nat.Prime.ne_zero
     assumption
