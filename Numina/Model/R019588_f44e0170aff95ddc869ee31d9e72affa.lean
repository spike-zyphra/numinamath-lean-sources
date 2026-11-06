import Mathlib

theorem number_theory_192404 (n m : ℤ) (hnm : n % 2 = 1 ∧ m % 2 = 1)
    (hdiv : 3 ∣ n ∧ 3 ∣ m) :
    72 ∣ (n^2 - m^2) := by
  have h1 : n % 2 = 1 := hnm.1
  have h2 : m % 2 = 1 := hnm.2
  have h3 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by 
    omega
  have h4 : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by 
    omega
  have h5 : n^2 % 8 = 1 := by
    rcases h3 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h] 
  have h6 : m^2 % 8 = 1 := by 
    rcases h4 with (h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h] 
  have h7 : (n^2 - m^2) % 8 = 0 := by 
    omega 
  -- Show divisibility by 9
  have h8 : 3 ∣ n := hdiv.1 
  have h9 : 3 ∣ m := hdiv.2 
  rcases h8 with ⟨k, hk⟩ 
  rcases h9 with ⟨l, hl⟩ 
  have h10 : n^2 - m^2 = 9 * (k^2 - l^2) := by 
    rw [show n = 3 * k by linarith, show m = 3 * l by linarith]
    ring_nf 
  have h8div : 8 ∣ (n ^ 2 - m ^ 2) := by 
    omega 
  have h9div : 9 ∣ (n ^ 2 - m ^ 2) := by 
    omega 
  omega