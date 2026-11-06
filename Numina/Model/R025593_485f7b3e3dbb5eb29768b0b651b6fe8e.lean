import Mathlib

theorem algebra_144446 {n : ℕ} (h : (n + 1) * (n + 2) = (n - 1) * (n - 2) + 600) :
    n = 100 := by
  by_cases h1 : n > 2
  · -- n > 2, so n - 1 and n - 2 are well-defined
    have h2 : n ≥ 3 := by omega
    have eq2 : (n + 1) * (n + 2) = (n - 1) * (n - 2) + 600 := h
    have eq5 : 6 * n = 600 := by
      cases n with
      | zero =>
        omega -- contradiction
      | succ n =>
        cases n with
        | zero =>
          omega -- contradiction
        | succ n =>
          cases n with
          | zero =>
            omega -- contradiction
          | succ n =>
            simp [Nat.mul_add, Nat.add_mul] at h ⊢
            ring_nf at h ⊢
            omega
    have eq6 : n = 100 := by
      omega
    exact_mod_cast eq6
  · -- n ≤ 2
    have h2 : n ≤ 2 := by omega
    interval_cases n <;> omega