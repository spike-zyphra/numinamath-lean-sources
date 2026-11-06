import Mathlib

/-Let $k$ be a positive integer. Suppose $m$ is a two-digit positive integer such that
$6^{-1}\pmod m$ exists and $6^{-1}\equiv 6^k\pmod m$. If $k=4$, show that $m=25$.-/

theorem number_theory_641951 (k m: ℕ) (h1: 10 ≤ m ∧ m < 100)
  (h2: ∃ x: ℕ, 6 * x % m = 1 ∧ x % m = 6 ^ k % m) (h3: k = 4): m = 25 := by
  simp [h3] at h2
  obtain ⟨x, s1, s2⟩ := h2
  rw [Nat.mul_mod] at s1
  simp [s2] at s1
  clear h3 s2
  rcases h1 with ⟨l, r⟩
  zify at s1
  replace s1: 7775 % m = 0 := by
    zify
    rw [show 7775 = 7776 - (1: ℤ) by norm_num]
    rw [Int.sub_emod]
    simp [s1]
    suffices (1: ℤ) % m = 1 by
      simp [this]
    apply Int.emod_eq_of_lt
    norm_num
    simp
    omega
  apply Nat.dvd_of_mod_eq_zero at s1
  replace s1: m ∈ Nat.divisors 7775 := by
    simp
    tauto
  rw [show Nat.divisors 7775 = {1, 5, 25, 311, 1555, 7775} by native_decide] at s1
  simp at s1
  omega
