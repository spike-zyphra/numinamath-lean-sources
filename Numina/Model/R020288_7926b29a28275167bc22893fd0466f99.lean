import Mathlib

theorem number_theory_105756 (n : ℕ) :
    100 ∣ 7^n + 7^(n + 1) + 7^(n + 2) + 7^(n + 3) ∧
    (n ≥ 4 → 10 ∣ (n - 4) * 7^n + (n - 3) * 7^(n + 1) +
      (n + 2) * 7^(n + 2) + (n - 1) * 7^(n + 3)) := by
  constructor
  · -- Prove the first part: 100 divides 7^n + 7^(n + 1) + 7^(n + 2) + 7^(n + 3)
    have h1 : 7^n + 7^(n + 1) + 7^(n + 2) + 7^(n + 3) = 400 * 7^n := by
      ring_nf
    rw [h1]
    use 4 * 7^n
    all_goals ring_nf
  · -- Prove the second part: (n ≥ 4 → 10 divides the expression)
    intro h
    have h2 : n ≥ 4 := h
    have h3 : (n - 4) * 7^n + (n - 3) * 7^(n + 1) + (n + 2) * 7^(n + 2) + (n - 1) * 7^(n + 3) = (400 * n - 270) * 7^n := by
      cases n with
      | zero =>
        omega
      | succ n =>
        cases n with
        | zero =>
          omega
        | succ n =>
          cases n with
          | zero =>
            omega
          | succ n =>
            cases n with
            | zero =>
              omega
            | succ n =>
              simp [pow_add, pow_mul, mul_add, add_mul]
              <;> ring_nf
    rw [h3]
    have h50 : (400 * n - 270) * 7^n = 10 * ((40 * n - 27) * 7^n) := by
      cases n with
      | zero =>
        omega
      | succ n =>
        cases n with
        | zero =>
          omega
        | succ n =>
          cases n with
          | zero =>
            omega
          | succ n =>
            cases n with
            | zero =>
              omega
            | succ n =>
              simp [pow_add, pow_mul, mul_add, add_mul]
              <;> ring_nf
    rw [h50]
    all_goals omega