import Mathlib

theorem number_theory_11558 (a : ℕ → ℕ) (ha : ∀ n, a n = (2 * n - 1) * (2 * n + 1) * (2 * n + 3)) :
    IsGreatest {d | ∀ i ∈ Finset.Icc 1 2008, d ∣ a i} 3 := by
  constructor
  · -- Show that 3 is in the set
    show ∀ i ∈ Finset.Icc 1 2008, 3 ∣ a i
    intro i hi
    rw [Finset.mem_Icc] at hi
    rcases hi with ⟨hi1, hi2⟩
    have h3 : a i = (2 * i - 1) * (2 * i + 1) * (2 * i + 3) := ha i
    rw [h3]
    have h4 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by
      omega
    rcases h4 with (h | h | h)
    · -- i ≡ 0 [MOD 3]
      have h5 : (2 * i + 3) % 3 = 0 := by
        omega
      have : ((2 * i - 1) * (2 * i + 1) * (2 * i + 3)) % 3 = 0 := by
        simp [Nat.mul_mod, h5]
      omega
    · -- i ≡ 1 [MOD 3]
      have h5 : (2 * i + 1) % 3 = 0 := by
        omega
      have : ((2 * i - 1) * (2 * i + 1) * (2 * i + 3)) % 3 = 0 := by
        simp [Nat.mul_mod, h5]
      omega
    · -- i ≡ 2 [MOD 3]
      have h5 : (2 * i - 1) % 3 = 0 := by
        omega
      have : ((2 * i - 1) * (2 * i + 1) * (2 * i + 3)) % 3 = 0 := by
        simp [Nat.mul_mod, h5]
      omega
  · -- Show that 3 is greatest
    intro d hd
    have h1 : ∀ i ∈ Finset.Icc 1 2008, d ∣ a i := hd
    have h2 := h1 1 (by simp)
    have h3 : a 1 = 15 := by
      rw [ha 1]
      all_goals norm_num
    rw [h3] at h2
    have h4 := h1 4 (by norm_num)
    have h5 : a 4 = 693 := by
      rw [ha 4]
      all_goals norm_num
    rw [h5] at h4
    -- Now, from $d \mid 15$ and $d \mid 693$, we have $d \mid \gcd(15, 693)$.
    -- $\gcd(15, 693) = 3$.
    have h6 : d ∣ 3 := by
      exact Nat.dvd_gcd h2 h4
    -- From $d \mid 3$, we have $d \leq 3$.
    have h7 : d ≤ 3 := by
      exact Nat.le_of_dvd (by linarith) h6
    linarith