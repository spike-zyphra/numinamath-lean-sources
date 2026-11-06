import Mathlib

theorem algebra_115975 (n : ℕ) (h : n > 0) (h' : ∑ i ∈ Finset.range (3 * n), (i + 1) = ∑ i ∈ Finset.range n, (i + 1) + 150) :
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
  --Now that's closed.

  have eq3 : ∑ i ∈ Finset.range (3 * n), (i + 1) = (3 * n) * (3 * n + 1) / 2 := by
    have h2 : ∀ k : ℕ, ∑ i ∈ Finset.range k, (i + 1) = k * (k + 1) / 2 := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring_nf
        <;> omega
    specialize h2 (3 * n)
    simpa using h2
  --Another important quadratic.
  have eq4 : ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := by
    have h2 : ∀ k : ℕ, ∑ i ∈ Finset.range k, (i + 1) = k * (k + 1) / 2 := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring_nf
        <;> omega
    specialize h2 n
    simpa using h2
  rw [eq3, eq4] at h'
  --Now from this, get unit expression in h_eq3
  have h_eq3 : (3 * n) * (3 * n + 1) = n * (n + 1) + 300 := by
    have h2 : (3 * n) * (3 * n + 1) % 2 = 0 := by
      have : (3 * n) * (3 * n + 1) % 2 = 0 := by
        have h11 : (3 * n) % 2 = 0 ∨ (3 * n) % 2 = 1 := by omega
        rcases h11 with (h11 | h11)
        · -- if (3n) is even
          simp [Nat.mul_mod, h11]
          <;> omega
        · -- if (3n) is odd
          have h12 : (3 * n + 1) % 2 = 0 := by
            omega
          simp [Nat.mul_mod, h11, h12]
          <;> omega
      omega
    --Second expression is even
    have h_eq2 : n * (n + 1) % 2 = 0 := by
      have : n * (n + 1) % 2 = 0 := by
        have h11 : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases h11 with (h11 | h11)
        · -- if n is even
          simp [Nat.mul_mod, h11]
          <;> omega
        · -- if n is odd
          have h12 : (n + 1) % 2 = 0 := by
            omega
          simp [Nat.mul_mod, h11, h12]
          <;> omega
      omega
    omega
  have h3 : n ≤ 12 := by nlinarith
  have h4 : n = 6 := by
    interval_cases n <;> omega
  have h5 : 4 * n = 24 := by
    omega
  have eq5 : ∑ i ∈ Finset.range (4 * n), (i + 1) = (4 * n) * (4 * n + 1) / 2 := by
    have h6 : ∀ k : ℕ, ∑ i ∈ Finset.range k, (i + 1) = k * (k + 1) / 2 := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring_nf
        <;> omega
    specialize h6 (4 * n)
    simpa using h6
  rw [eq5]
  rw [h5]
  all_goals norm_num
  all_goals omega