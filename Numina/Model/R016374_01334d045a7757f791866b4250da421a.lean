import Mathlib

theorem number_theory_249938 (A : ℕ → ℕ)
    (hA : ∀ k, A k = 5^(2*k + 1) * 2^(k + 2) + 3^(k + 2) * 2^(2*k + 1)) :
    ∀ k, 19 ∣ A k := by
  intro k
  induction k with
  | zero =>
    have h1 : A 0 = 5 ^ 1 * 2 ^ 2 + 3 ^ 2 * 2 ^ 1 := by
      specialize hA 0
      norm_num at hA ⊢
      all_goals omega
    rw [h1]
    all_goals norm_num
  | succ n ih =>
    have h2 : A (n + 1) = 5 ^ (2 * (n + 1) + 1) * 2 ^ ((n + 1) + 2) + 3 ^ ((n + 1) + 2) * 2 ^ (2 * (n + 1) + 1) := by
      specialize hA (n + 1)
      simpa using hA
    rw [h2]
    have h3 : 5 ^ (2 * (n + 1) + 1) * 2 ^ ((n + 1) + 2) + 3 ^ ((n + 1) + 2) * 2 ^ (2 * (n + 1) + 1) =
      50 * (5 ^ (2 * n + 1) * 2 ^ (n + 2)) + 12 * (3 ^ (n + 2) * 2 ^ (2 * n + 1)) := by
      ring_nf
    rw [h3] at *
    -- rewrite the goal using A_{n+1} = 50 * x + 12 * y and the hypothesis that 19 divides x + y
    have h4 : (50 * (5 ^ (2 * n + 1) * 2 ^ (n + 2)) + 12 * (3 ^ (n + 2) * 2 ^ (2 * n + 1))) % 19 = 0 := by
      have h5 : (5 ^ (2 * n + 1) * 2 ^ (n + 2) + 3 ^ (n + 2) * 2 ^ (2 * n + 1)) % 19 = 0 := by
        have h6 : 19 ∣ A n := ih
        have h7 : A n = 5 ^ (2 * n + 1) * 2 ^ (n + 2) + 3 ^ (n + 2) * 2 ^ (2 * n + 1) := by
          specialize hA n
          simpa using hA
        rw [h7] at h6
        omega
      omega
    omega