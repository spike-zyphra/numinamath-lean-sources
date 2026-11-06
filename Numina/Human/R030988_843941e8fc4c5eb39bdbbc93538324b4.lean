import Mathlib

/- 1. If the square of any natural number is increased by the number 101010, then the resulting sum cannot be a square of a natural number. Prove! -/
theorem number_theory_226525 (n : ℕ) :
  ¬ ∃ m, n^2 + 101010 = m^2
:= by
  rw [not_exists]
  -- Suppose for the sake of contradiction that there exists m such that n^2 + 101010 = m^2
  intro m h

  -- Factoring, we have 101010 = (m + n) * (m - n)
  replace h : (↑m + ↑n) * (↑m - ↑n) = (101010 : ℤ) := by
    ring_nf
    rw_mod_cast [<-h]
    apply Int.subNatNat_add_left

  -- We do casework on the parity of m and n
  mod_cases hn : (↑n : ℤ) % 2 <;>
    rw [Int.modEq_comm, Int.modEq_iff_add_fac] at hn <;>
    rcases hn with ⟨t, hn⟩ <;>
  mod_cases hm : (↑m : ℤ) % 2 <;>
    rw [Int.modEq_comm, Int.modEq_iff_add_fac] at hm <;>
    rcases hm with ⟨s, hm⟩ <;>
  rw [hn, hm] at h <;>
  clear hn hm <;>
  ring_nf at h

  -- If m and n are both even, then (m + n) * (m - n) is divisible by 4, which is a contradiction.
  · have h_bad : 4 ∣ (101010 : ℤ) := by
      simp [<- h, <- sub_mul]
    simp +decide at h_bad
  -- If m and n not the same parity, then (m + n) * (m - n) is odd, which is a contradiction
  · have h_bad : 4 ∣ (101010 - 1: ℤ) := by
      simp [<- h]
      ring_nf
      simp [<- sub_mul, <- add_mul]
    simp +decide at h_bad
  · have h_bad : 4 ∣ (101010 + 1: ℤ) := by
      simp [<- h]
      ring_nf
      rw [neg_mul_eq_neg_mul, <- sub_mul, <- add_mul]
      simp
    simp +decide at h_bad
  -- If m and n are both odd, then (m + n) * (m - n) is divisible by 4, which is a contradiction.
  · have h_bad : 4 ∣ (101010 : ℤ) := by
      simp [<- h]
      ring_nf
      rw [neg_mul_eq_neg_mul, <- sub_mul, <- add_mul, <- add_mul]
      simp
    simp +decide at h_bad