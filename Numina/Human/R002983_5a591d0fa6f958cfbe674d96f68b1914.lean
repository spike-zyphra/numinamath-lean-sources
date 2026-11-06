import Mathlib

/- 14.2.11 ** Find two coprime four-digit positive integers $A$ and $B$, such that for any positive integers $m$ and $n$, the numbers $A^{m}$ and $B^{n}$ differ by at least 4000, -/
theorem number_theory_138924 :
    ∃ A B : ℕ, A ∈ Set.Ico 1000 10000 ∧ B ∈ Set.Ico 1000 10000 ∧ Nat.Coprime A B ∧
      ∀ m n : ℕ, 0 < m → 0 < n → |(A ^ m : ℤ) - (B ^ n)| ≥ 4000 := by 
  -- Take $A = 8001$, $B = 4001$.
  use 4001, 8001, by simp, by simp
  have h : Nat.Coprime 4001 8001 := by decide
  constructor
  · exact h
  · intro m n hm hn
    show |4001 ^ m - 8001 ^ n| ≥ 4000
    -- For any positive integers $m$ and $n$, $A^m$, $B^n$ when divided by $4000$ both leave a remainder of $1$,  
    have h2 : 4001 ^ m % 4000 = 1 := by
      rw [Nat.pow_mod]
      simp
    have h3 : 8001 ^ n % 4000 = 1 := by
      rw [Nat.pow_mod]
      simp
    -- so $A^m - B^n$ are all multiples of $4000$.
    have h4 : (4000 : ℤ) ∣ 4001 ^ m - 8001 ^ n := by
      suffices Int.ofNat 4000 ∣ Int.ofNat (4001 ^ m) - Int.ofNat (8001 ^ n) by simp_all
      apply Nat.ModEq.dvd
      rw [Nat.ModEq.eq_1]
      simp_all
    obtain ⟨k, hk⟩ : ∃ k : ℤ, 4001 ^ m - 8001 ^ n = 4000 * k := by
      rw [← Int.dvd_def]
      exact h4
    -- Since $A^m \ne B^n$, it follows that $|A^m - B^n| \geq 4000$.
    have h5 : 4001 ^ m ≠ 8001 ^ n := by
      rintro heq
      apply Nat.Coprime.pow m n at h
      rw [heq, Nat.coprime_self] at h
      rw [pow_eq_one_iff (by linarith)] at h
      simp at h
    have h6 : (4001 : ℤ) ^ m - 8001 ^ n ≠ 0 := by 
      intro h
      apply h5
      rw [← Int.ofNat.injEq]
      simp_all
      linarith
    have h7 : Int.natAbs 4000 ≤ Int.natAbs (4001 ^ m - 8001 ^ n) := by 
      apply Int.natAbs_le_of_dvd_ne_zero h4 h6
    suffices ((4000 : ℕ) : ℤ) ≤ |4001 ^ m - 8001 ^ n| by simp_all
    rw [Int.abs_eq_natAbs, Int.ofNat_le]
    simp_all