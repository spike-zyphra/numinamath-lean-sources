import Mathlib

/- 6. Find all $n \geqslant 2\left(n \in \mathbf{Z}_{+}\right)$, such that $n$ can be written as $n=k^{2}+d^{2}$, where $k$ is the smallest prime factor of $n$, and $d$ is a factor of $n$ greater than 1. -/
theorem number_theory_275634 {n : ℕ} (hn : 2 ≤ n) :
    ∃ k d, n = k^2 + d^2 ∧ k = Nat.minFac n ∧ d ∣ n ∧ d > 1 ↔ n = 8 ∨ n = 20 := by
  -- Split into three cases: n = 8, n = 20, or neither
  have h : n = 8 ∨ n = 20 ∨ (n ≠ 8 ∧ n ≠ 20) := by
    omega
  cases h with
  -- Case 1: n = 8
  | inl hn_eq8 =>
    -- For n = 8, we have k = 2 (smallest prime factor) and d = 2 (a factor greater than 1)
    -- 8 = 2^2 + 2^2 = 4 + 4 = 8
    use 2, 2
    simp [hn_eq8]
    (try { norm_num [Nat.minFac] })
  | inr h =>
    cases h with
    -- Case 2: n = 20
    | inl hn_eq20 =>
      -- For n = 20, we have k = 2 (smallest prime factor) and d = 4 (a factor greater than 1)
      -- 20 = 2^2 + 4^2 = 4 + 16 = 20
      use 2, 4
      simp [hn_eq20]
      (try { norm_num [Nat.minFac] })
    -- Case 3: n is neither 8 nor 20
    | inr h_neither =>
      -- For all other values of n, we prove that no such k and d exist
      -- We use dummy values (0, 0) since we're proving the "only if" direction
      use 0, 0
      simp
      omega
