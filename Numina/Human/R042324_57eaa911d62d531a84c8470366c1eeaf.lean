import Mathlib

/- Let a_{10} = 10, and for each positive integer n>10 let a_n=100a_{n−1}+n.
Find the least positive n>10 such that a_n​ is a multiple of 99. -/
theorem number_theory_97149 (a : ℕ → ℕ)
    (h₀ : a 10 = 10) (h₁ : ∀ n > 10, a n = 100 * a (n - 1) + n) :
    IsLeast {n | 10 < n ∧ 99 ∣ a n} 45 := by
  -- show that 2 * a (n + 10) = 99 * k + (n + 20) * (n + 1) for some k ∈ ℕ
  have ha n : ∃ k, 2 * a (n + 10) = 99 * k + (n + 20) * (n + 1) := by
    -- proof by induction
    induction n with
    -- k = 0 for a 10
    | zero => use 0; rw [h₀]
    | succ n ih =>
      -- we have 2 * a (n + 10) = 99 * k + (n + 20) * (n + 1)
      have ⟨k, hk⟩ := ih
      -- we need to find k' such that 2 * a(n + 11) = 99 * k' + (n + 21) * (n + 2)
      -- use k' = 100 * k + n * (n + 21) + 20
      use 100 * k + n * (n + 21) + 20
      rw [h₁ _ (by omega), show n + 1 + 10 - 1 = n + 10 by omega]
      rw [show ∀ a b, 2 * (100 * a + b) = 100 * (2 * a) + 2 * b by omega]
      rw [hk]
      ring
  -- now we can show that 99 divides a (n + 10) iff 99 divides (n + 20) * (n + 1)
  have ha_dvd n : 99 ∣ a (n + 10) ↔ 99 ∣ (n + 20) * (n + 1) := by
    have ⟨k, hk⟩ := ha n
    rw [← Nat.Coprime.dvd_mul_left (show (99).Coprime 2 by norm_num), hk]
    rw [← Nat.dvd_add_iff_right]
    use k
  -- we need to show that 99 ∣ a 45 and when 99 ∣ a (n + 10) then n + 10 ≥ 45
  simp [IsLeast, lowerBounds]
  -- 99 ∣ a 45 follows from 99 ∣ (35 + 20) * (35 + 1) (here, n + 10 = 45, so n = 35)
  rw [ha_dvd 35]
  norm_num
  intro n' hn
  set n := n' - 10
  replace hn : n' = n + 10 := by omega
  -- we have 99 ∣ a (n + 10), so 99 ∣ (n + 20) * (n + 1)
  rw [hn, ha_dvd]
  -- the proof can be finished with omega by considering all possible values of n ≤ 34
  -- by_contra h1
  -- push_neg at h1
  -- have h2 : n ≤ 34 := by omega
  -- interval_cases n <;> omega
  intro h99
  -- 99 ∣ (n + 20) * (n + 1) so 11 ∣ (n + 20) * (n + 1)
  have h11 : 11 ∣ (n + 20) * (n + 1) := by
    have ⟨k, hk⟩ := h99
    use 9 * k
    rw [hk]
    ring
  -- 11 is prime so we can consider two cases: 11 ∣ n + 20 and 11 ∣ n + 1
  rw [Nat.Prime.dvd_mul (by norm_num)] at h11
  rcases h11 with ⟨k, hk⟩ | ⟨k, hk⟩
  -- if 11 ∣ n + 20 then n = k * 11 - 20
  -- consider two cases: k ≤ 4 and k > 4
  · cases' le_or_gt k 4 with h h
    -- if k ≤ 4 then consider all cases k = 0, k = 1, k = 2, k = 3, k = 4
    -- and show that 99 does not divide (n + 20) * (n + 1)
    · rw [show n = 11 * k - 20 by omega] at h99
      interval_cases k <;> norm_num at h99
    -- if k ≥ 5 then n + 10 ≥ 55 - 20 + 10 = 45
    · omega
  -- if 11 ∣ n + 1 then n = k * 11 - 1
  -- consider two cases: k ≤ 3 and k > 4
  · cases' le_or_gt k 3 with h h
    -- if k ≤ 3 then consider all cases k = 0, k = 1, k = 2, k = 3
    -- and show that 99 does not divide (n + 20) * (n + 1)
    · rw [show n = 11 * k - 1 by omega] at h99
      interval_cases k <;> norm_num at h99
    -- if k ≥ 4 then n + 10 ≥ 44 - 1 + 10 ≥ 45
    · omega