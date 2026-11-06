import Mathlib

theorem number_theory_318925 {n : ℕ} (hn : n > 0) (h : n * n - (n - 1) * (n - 1) = 37) :
    n ^ 2 = 361 := by
  have h1 : n ≥ 2 := by
    by_contra h2
    push_neg at h2
    have : n = 1 := by
      interval_cases n <;> tauto
    rw [this] at h
    all_goals
      omega
  have eq1 : n * n - (n - 1) * (n - 1) = 2 * n - 1 := by
    cases n with
    | zero =>
      omega
    | succ n =>
      cases n with
      | zero =>
        all_goals omega
      | succ n =>
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.sub_sub, Nat.add_assoc] at *
        <;> ring_nf <;> omega
  rw [eq1] at h
  have hn19 : n = 19 := by
    omega
  calc
    n ^ 2 = 19 ^ 2 := by rw [hn19]
    _ = 361 := by norm_num