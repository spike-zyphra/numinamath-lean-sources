import Mathlib

theorem algebra_96311 (n : ℕ) (h : n > 0) (h' : ∑ i ∈ Finset.range (3 * n), (i + 1) = ∑ i ∈ Finset.range n, (i + 1) + 150) :
    ∑ i ∈ Finset.range (4 * n), (i + 1) = 300 := by

  have h1 : ∀ k : ℕ, ∑ i ∈ Finset.range k, (i + 1) = k * (k + 1) / 2 := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring_nf
      <;> omega

  have eq1 : ∑ i ∈ Finset.range (3 * n), (i + 1) = (3 * n) * (3 * n + 1) / 2 := by
    apply h1

  have eq2 : ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := by
    apply h1
  rw [eq1, eq2] at h'

  have h2 : n = 6 := by
    have eq3 : (3 * n) * (3 * n + 1) = n * (n + 1) + 300 := by
      have h11 : (3 * n) * (3 * n + 1) % 2 = 0 := by
        have : (3 * n) * (3 * n + 1) % 2 = 0 := by
          have h11 : (3 * n) % 2 = 0 ∨ (3 * n) % 2 = 1 := by omega
          have h12 : (3 * n + 1) % 2 = 0 ∨ (3 * n + 1) % 2 = 1 := by omega
          rcases h11 with (h11 | h11)
          <;> rcases h12 with (h12 | h12)
          <;> simp [Nat.mul_mod, Nat.add_mod, h11, h12]
          <;> omega
        omega
      have h12 : (n * (n + 1) + 300) % 2 = 0 := by
        have hn1 : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases hn1 with (hn1 | hn1)
        · -- Case n is even
          have h12 : n * (n + 1) % 2 = 0 := by
            simp [Nat.mul_mod, Nat.add_mod, hn1]
          omega
        · -- Case n is odd
          have h12 : n * (n + 1) % 2 = 0 := by
            have h11 : (n + 1) % 2 = 0 := by
              omega
            simp [Nat.mul_mod, Nat.add_mod, h11]
          omega
      omega
    have eq4 : n = 6 := by
      nlinarith [sq_nonneg (n : ℕ), sq_nonneg ((3 * n) : ℕ),
        sq_nonneg ((n - 6 : ℤ)), sq_nonneg ((4 * n + 24 : ℤ)),
        sq_nonneg ((n * 3) : ℕ), sq_nonneg ((n + 6) : ℤ)]
    exact_mod_cast eq4
  -- calculating sum using n = 6.
  have eq4 : ∑ i ∈ Finset.range (4 * n), (i + 1) = (4 * n) * (4 * n + 1) / 2 := by
    apply h1
  rw [eq4]
  rw [h2]
  all_goals norm_num