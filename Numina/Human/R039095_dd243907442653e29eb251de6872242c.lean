import Mathlib

theorem number_theory_190193 :
    IsGreatest {k | ∃ n : ℕ, 0 < n ∧ 3^11 = ∑ i ∈ Finset.range k, (n + i)} 486 := by
  constructor
  · use 122
    native_decide
  · rintro k ⟨n, hn, hsum⟩
    apply_fun (· * 2) at hsum
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, add_mul, Finset.sum_range_id_mul_two, mul_assoc, ← mul_add] at hsum
    have hk : k ≤ n * 2 + (k - 1) := by omega
    have h₁ : k ^ 2 ≤ 3 ^ 11 * 2 := by nlinarith
    have h₂ : k ≤ Nat.sqrt (3 ^ 11 * 2) := Nat.le_sqrt'.mpr h₁
    have h₃ : k ∣ 3 ^ 11 * 2 := by simp only [hsum, dvd_mul_right]
    replace h₃ : k ∈ Nat.divisors (3 ^ 11 * 2) := Nat.mem_divisors.mpr ⟨h₃, by simp⟩
    suffices H : ∀ k ∈ Nat.divisors (3 ^ 11 * 2), k ≤ (3 ^ 11 * 2).sqrt → k ≤ 486 from H k h₃ h₂
    native_decide