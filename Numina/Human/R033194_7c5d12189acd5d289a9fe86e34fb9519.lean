import Mathlib

/-Xiao Guang's home phone number is an eight-digit number.
The first four digits are the same, and the last five digits are consecutive one-digit natural numbers.
The sum of the digits of the phone number equals its last two digits. Therefore, this phone number is .-/

theorem number_theory_624683 (n : ℤ) (a1 a2 a3 a4 a5 a6 a7 a8 : ℤ)
(hn: n = a8 * 10^7 + a7 * 10^6 + a6 * 10^5 + a5 * 10^4 + a4 * 10^3 + a3 * 10^2 + a2 * 10^1 + a1)
(l1: 0 ≤ a1 ∧ a1 ≤ 9) (l4: 0 ≤ a4 ∧ a4 ≤ 9) (l8: 1 ≤ a8 ∧ a8 ≤ 9)
(h1: a8 = a7) (h2: a7 = a6) (h3: a6 = a5)
(h4: (a4 = a5 + 1 ∧ a3 = a4 + 1 ∧ a2 = a3 + 1 ∧ a1 = a2 + 1) ∨ (a4 = a5 - 1 ∧ a3 = a4 - 1 ∧ a2 = a3 - 1 ∧ a1 = a2 - 1))
(h5: a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 = a2 * 10 + a1): n = 88887654 := by

    let a:= a8
    replace h1: a7 = a := by
        simp [h1, a]
    replace h2: a6 = a := by
        rw [← h2]
        rw [h1]
    replace h3: a5 = a := by
        rw [← h3]
        rw [h2]
    rcases h4 with h | h
    -- case 1
    .
        rcases h with ⟨s4, s3, s2, s1⟩
        replace s4: a4 = a + 1 := by
            rw [s4]
            rw [h3]
        replace s3: a3 = a + 2 := by
            rw [s3]
            rw [s4]
            omega
        replace s2: a2 = a + 3 := by
            rw [s2]
            rw [s3]
            omega
        replace s1: a1 = a + 4 := by
            rw [s1]
            rw [s2]
            omega
        simp [h1, h2, h3, s4, s3, s2, s1] at *
        ring_nf at h5
        replace h5: a = -8 := by omega
        rw [h5] at l1
        norm_num at l1
    -- case 2
    .
        rcases h with ⟨s4, s3, s2, s1⟩
        replace s4: a4 = a - 1 := by
            rw [s4]
            rw [h3]
        replace s3: a3 = a - 2 := by
            rw [s3]
            rw [s4]
            omega
        replace s2: a2 = a +- 3 := by
            rw [s2]
            rw [s3]
            omega
        replace s1: a1 = a - 4 := by
            rw [s1]
            rw [s2]
            omega
        simp [h1, h2, h3, s4, s3, s2, s1] at *
        ring_nf at h5
        replace h5: a = 8 := by omega
        simp [a, h5] at hn
        simp [a] at h5
        simp [h5] at hn
        exact hn
        