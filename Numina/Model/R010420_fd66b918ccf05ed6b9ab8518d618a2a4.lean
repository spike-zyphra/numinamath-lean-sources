import Mathlib

theorem number_theory_240527 (n : ℤ) (hn : Odd n ∧ n > 0) :
    2^9 ∣ n^12 - n^8 - n^4 + 1 := by
  have h1 : n % 2 = 1 := by
    rcases hn with ⟨hodd, _⟩
    rcases hodd with ⟨k, hk⟩
    omega
  have h2 : n ^ 4 % 16 = 1 := by
    have h3 : n % 2 = 1 := h1
    have h4 : n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨ n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by
      omega
    rcases h4 with (h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod, h] at *
  have h5 : (n ^ 4 - 1) % 16 = 0 := by
    omega
  have h6 : 16 ∣ n ^ 4 - 1 := by
    omega
  have h8 : 2 ∣ n ^ 4 + 1 := by
    omega
  have h9 : 16 ∣ n ^ 4 - 1 := h6
  have h10 : 2 ∣ n ^ 4 + 1 := h8
  have h11 : 16 * 16 ∣ (n ^ 4 - 1) ^ 2 := by
    apply pow_dvd_pow_of_dvd h9 2
  have h12 : 2 ^ 9 ∣ (n ^ 4 - 1) ^ 2 * (n ^ 4 + 1) := by
    have h13 : 16 * 16 ∣ (n ^ 4 - 1) ^ 2 := h11
    have h14 : 2 ∣ n ^ 4 + 1 := h10
    have h16 : (16 * 16 : ℤ) * 2 ∣ (n ^ 4 - 1) ^ 2 * (n ^ 4 + 1) := by
      apply mul_dvd_mul h13 h14
    norm_num at h16 ⊢
    apply h16
  have h15 : (n ^ 4 - 1) ^ 2 * (n ^ 4 + 1) = n^12 - n^8 - n^4 + 1 := by
    ring
  rw [h15] at h12
  exact h12