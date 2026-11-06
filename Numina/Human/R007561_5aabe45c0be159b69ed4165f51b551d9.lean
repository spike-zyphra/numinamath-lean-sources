import Mathlib

/-
PROBLEM: What is the largest positive integer n for which n^3+100 is divisible by n+10?
-/

theorem number_theory_94999 :
IsGreatest {n : ℕ | 0 < n ∧ (n^3 + 100) % (n + 10) = 0} 890 := by {
  -- n = 890 satisfies the condition
  rw [IsGreatest]
  constructor
  simp
  -- Any number n that satisfies the condition is at most 890
  rw [mem_upperBounds]
  intros n h
  simp at h
  rcases h with ⟨hg0, h⟩
  suffices : (n + 10) ∣ 900
  apply Nat.le_of_add_le_add_right _
  use 10
  apply Nat.le_of_dvd
  trivial
  exact this
  let nz := (n : ℤ)
  have h100 : (100 : ℕ) = (100 : ℤ) := by trivial
  
  -- Transfer to the integers for nicer modular arithmetic
  have hmod : (nz^3 + 100) ≡ 0 [ZMOD (nz + 10)] := by {
    unfold Int.ModEq
    simp
    unfold nz
    rw [←Nat.cast_ofNat, ←Nat.cast_ofNat, ←Int.natCast_add, ←Int.natCast_pow, ←h100, 
        ←Int.natCast_add, Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero]
    trivial
  }

  -- Apply Euclidean algorithm / polynomial long division
  have hzfac : nz^3 + 100 = (nz^2 - 10*nz + 100)*(nz + 10) - 900 := by ring
  rw [hzfac] at hmod
  have : 900 ≡ 0 [ZMOD (nz + 10)] := by {
    rw [Int.sub_eq_add_neg, add_comm ((nz^2 - 10*nz + 100)*(nz + 10)) (-900), mul_comm] at hmod
    apply (Int.modEq_add_fac) at hmod
    swap
    use -(nz^2 - 10*nz + 100)
    ring_nf at hmod
    ring_nf
    rw [Int.modEq_zero_iff_dvd]
    rw [Int.modEq_zero_iff_dvd, Int.dvd_neg] at hmod
    exact hmod
  }

  -- Return to natural numbers and conclude
  unfold nz at this
  have h900 : (900 : ℕ) = (900 : ℤ) := by trivial
  have h0 : (0 : ℕ) = (0 : ℤ) := by trivial
  rw [←Nat.cast_ofNat, ←h900, ←h0, ←Int.natCast_add n 10, Int.natCast_modEq_iff] at this
  have h0900 : 0 ≤ 900 := by trivial
  apply Nat.modEq_iff_dvd' at h0900
  swap
  use n + 10
  simp at h0900
  rw [←h0900]
  apply Nat.ModEq.symm
  exact this
}