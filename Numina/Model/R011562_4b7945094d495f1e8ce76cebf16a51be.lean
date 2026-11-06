import Mathlib

theorem number_theory_258338 (n : ℤ) :
    ¬ ∃ m, m^2 = n^2 + (n+1)^2 + (n+2)^2 + (n+3)^2 + (n+4)^2 +
      (n+5)^2 + (n+6)^2 + (n+7)^2 + (n+8)^2 + (n+9)^2 := by
  rintro ⟨m, hm⟩
  have eq1 : m^2 = 10 * n^2 + 90 * n + 285 := by 
    nlinarith
  have eq2 : m^2 = 5 * (2 * n^2 + 18 * n + 57) := by 
    nlinarith
  have h1 : m^2 % 5 = 0 ∨ m^2 % 5 = 1 ∨ m^2 % 5 = 4 := by
    have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
      omega
    rcases h1 with (h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h]
  have eq3 : m^2 % 5 = 0 := by 
    omega
  have eq4 : m % 5 = 0 := by
    have h1 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
      omega
    rcases h1 with (h | h | h | h | h) <;> norm_num [h, pow_two, Int.add_emod, Int.mul_emod] at eq3 ⊢ <;> omega
  have eq5 : ∃ k : ℤ, m = 5 * k := by
    have : m % 5 = 0 := eq4
    have : 5 ∣ m := by omega
    rcases this with ⟨k, hk⟩
    exact ⟨k, by linarith⟩
  rcases eq5 with ⟨k, hk⟩
  rw [hk] at eq2
  have eq6 : 25 * k^2 = 5 * (2 * n^2 + 18 * n + 57) := by
    nlinarith
  have eq7 : 5 * k^2 = 2 * n^2 + 18 * n + 57 := by 
    nlinarith
  have eq8 : (2 * n^2 + 18 * n + 57 : ℤ) % 5 = 0 := by
    omega
  have : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega
  rcases this with (h | h | h | h | h) <;> norm_num [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod] at eq8