import Mathlib

/- Let $a$ be an integer greater than $1$. Show that it is not the case that for all natural numbers $n$,
the number $a^{2n+1}-1$ is prime.-/

theorem number_theory_636187 (a: ℤ) (ha: 1 < a): ¬ ∀ n, Prime (a ^ (2 * n + 1) - 1) := by

  by_contra! h

  by_cases l: a = 2

  -- case when a = 2
  .
    simp [l] at h
    specialize h 4
    simp at h
    norm_num at h

  -- case when a > 2
  .
    replace ha: 3 ≤ a := by omega
    clear l
    specialize h 1
    simp at h
    rw [show a ^ 3 - 1 = (a - 1) * (a ^ 2 + a + 1) by ring] at h
    set p:= a - 1
    set q:= a ^ 2 + a + 1
    have hp: 1 < p := by omega
    have hq: 1 < q := by
      simp [q]
      nlinarith
    set p':= p.natAbs
    set q':= q.natAbs
    have hp': 1 < p' := by
      simp [p']
      omega
    have hq': 1 < q' := by
      simp [q']
      omega
    have o: Nat.Prime (p' * q') := by
      rw [Int.prime_iff_natAbs_prime] at h
      rw [Int.natAbs_mul] at h
      tauto
    rw [Nat.prime_mul_iff] at o
    omega


