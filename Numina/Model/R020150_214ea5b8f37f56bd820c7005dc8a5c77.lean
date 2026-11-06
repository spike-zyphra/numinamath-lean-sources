import Mathlib

theorem algebra_130103 {a : ℕ → ℤ} (ha0 : a 0 = 2) (ha1 : a 1 = 3) (ha2 : a 2 = 6)
    (han : ∀ n ≥ 3, a n = (n + 4) * a (n - 1) - 4 * n * a (n - 2) + (4 * n - 8) * a (n - 3)) :
    ∀ n, a n = Nat.factorial n + 2 ^ n := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  cases n with
  | zero =>
    rw [ha0]
    simp [Nat.factorial]
    <;> try { tauto }
  | succ n =>
    cases n with
    | zero =>
      rw [ha1]
      simp [Nat.factorial]
      <;> try { tauto }
    | succ n =>
      cases n with
      | zero =>
        rw [ha2]
        simp [Nat.factorial]
        <;> try { tauto }
      | succ n =>
        have h3 := han (n + 3) (by linarith)
        simp [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega, show n + 3 - 3 = n by omega] at h3
        have ih1 := ih (n + 2) (by linarith)
        have ih2 := ih (n + 1) (by linarith)
        have ih3 := ih (n) (by linarith)
        simp [h3, ih1, ih2, ih3, Nat.factorial]
        <;> try { ring_nf }
        <;> try { 
          omega
        }
        <;> try { 
          native_decide
        }