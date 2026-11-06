import Mathlib

theorem number_theory_75419 (k m n : ℤ) (hk : 0 < k) (hm : 0 < m) (hn : 0 < n)
    (hdiv : ¬(5 ∣ k) ∧ ¬(5 ∣ m) ∧ ¬(5 ∣ n)) :
    5 ∣ k^2 - m^2 ∨ 5 ∣ m^2 - n^2 ∨ 5 ∣ n^2 - k^2 := by

  have hk1 : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by
    omega

  have hm1 : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by 
    omega

  have hn1 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by 
    omega

  have h1 : k^2 % 5 = 1 ∨ k^2 % 5 = 4 := by
    rcases hk1 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]

  have h2 : m^2 % 5 = 1 ∨ m^2 % 5 = 4 := by 
    rcases hm1 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]

  have h3 : n^2 % 5 = 1 ∨ n^2 % 5 = 4 := by 
    rcases hn1 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]

  omega