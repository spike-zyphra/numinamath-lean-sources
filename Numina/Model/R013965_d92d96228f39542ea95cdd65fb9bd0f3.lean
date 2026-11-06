import Mathlib

theorem algebra_202704 {n : ℕ} (hn : n > 0) :
    (Nat.factorial (n + 2) - Nat.factorial (n + 1) - Nat.factorial n) / Nat.factorial n = 2024 ↔ n = 44 := by
  constructor
  · -- Assume $\frac{(n+2)!-(n+1)!-n!}{n!}=2024$, then $n = 44$
    intro h
    have eq1 : Nat.factorial (n + 2) = (n + 2) * (n + 1) * Nat.factorial n := by
      simp [Nat.factorial]
      <;> ring_nf
    have eq2 : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
      simp [Nat.factorial]
      <;> ring_nf
    have eq3 : Nat.factorial (n + 2) - Nat.factorial (n + 1) - Nat.factorial n = Nat.factorial n * (n ^ 2 + 2 * n) := by
      rw [eq1, eq2]
      ring_nf
      <;> omega
    have eq4 : Nat.factorial n > 0 := by positivity
    have eq5 : (Nat.factorial (n + 2) - Nat.factorial (n + 1) - Nat.factorial n) / Nat.factorial n = n ^ 2 + 2 * n := by
      rw [eq3]
      field_simp [eq4]
      <;> ring_nf
    rw [eq5] at h
    have h1 : n ≤ 45 := by
      by_contra h2
      push_neg at h2
      have h3 : n ^ 2 + 2 * n > 2024 := by
        nlinarith
      omega
    interval_cases n <;> omega
  · -- Assume n = 44, prove $\frac{(n+2)!-(n+1)!-n!}{n!}=2024$
    intro h
    rw [h]
    native_decide