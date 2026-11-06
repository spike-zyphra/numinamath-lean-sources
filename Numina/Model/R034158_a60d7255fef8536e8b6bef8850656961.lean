import Mathlib

theorem number_theory_607564 (n : ℕ) (h : ∃ k : ℕ, 2 ^ n = 2 ^ k * n) : ∃ t : ℕ, n = 2 ^ t := by
  rcases h with ⟨k, hk⟩
  have eq2 : n ∣ 2 ^ n := by
    use 2 ^ k
    all_goals
      nlinarith [hk]
  -- Let's first show that $n > 0$.
  have h100 : n > 0 := by
    by_contra h'
    have eq33 : n = 0 := by omega
    rw [show n = 0 by omega] at hk
    norm_num at hk
  -- Now, show that $k \leq n$.
  have h44 : k ≤ n := by
    by_contra h'
    push_neg at h'
    have h99 : k > n := by omega
    have h10 : 2 ^ k > 2 ^ n := by
      have h11 : k > n := h99
      have h12 : 2 ^ k > 2 ^ n := by
        apply Nat.pow_lt_pow_right
        all_goals
          omega
      linarith
    have h11 : 2 ^ k * n ≥ 2 ^ k := by
      have h88 : n ≥ 1 := by omega
      nlinarith [show 2 ^ k > 0 by
        apply Nat.pow_pos
        norm_num
      ]
    nlinarith [hk, h10, h11]
  -- Now from the equation $2^n = 2^k \cdot n$, we rearrange to get $2^{n-k} = n$.
  -- Let's take $t = n-k$.
  use n - k
  have eq55 : 2 ^ (n - k) = n := by
    have eq66 : k ≤ n := h44
    have h_eq1 : 2 ^ n = 2 ^ k * n := hk
    have h_eq2 : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by
      have h99 : k ≤ n := h44
      have h_eq3 : 2 ^ n = 2 ^ (k + (n - k)) := by
        rw [show k + (n - k) = n by
          omega
        ]
      have h_eq4 : 2 ^ (k + (n - k)) = 2 ^ k * 2 ^ (n - k) := by
        ring_nf
      rw [h_eq4] at h_eq3
      exact h_eq3
    have h99 : 2 ^ k > 0 := by
      apply Nat.pow_pos
      norm_num
    have h_eq5 : 2 ^ (n - k) = n := by
      have h3 : 2 ^ k * 2 ^ (n - k) = 2 ^ k * n := by
        nlinarith [h_eq1, h_eq2]
      have h999 : 2 ^ k > 0 := h99
      have h1010 : 2 ^ (n - k) = n := by
        nlinarith
      exact h1010
    exact h_eq5
  -- Now, since $2^{n-k} = n$, we have $n$ is a power of 2.
  nlinarith [eq55]