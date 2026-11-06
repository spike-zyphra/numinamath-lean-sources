import Mathlib

theorem number_theory_14601 :
    IsGreatest {y | ∀ x : ℤ, Odd x → y ∣ (10 * x + 2) * (10 * x + 6) * (5 * x + 5)} 960 := by 
  constructor 
  · -- Show 960 is in the set
    show ∀ x : ℤ, Odd x → 960 ∣ (10 * x + 2) * (10 * x + 6) * (5 * x + 5)
    intro x hx 
    have h1 : x % 2 = 1  := by 
      obtain ⟨k, hk⟩ := hx 
      omega
    have h10 : (10 * x + 2) * (10 * x + 6) * (5 * x + 5) % 3 = 0 := by 
      have h1' : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2  := by omega
      rcases  h1' with (h | h | h)
      all_goals 
        simp [Int.mul_emod, Int.add_emod, h, Int.mul_emod, Int.add_emod]
    have h11 : (10 * x + 2) * (10 * x + 6) * (5 * x + 5) % 5 = 0  := by
      have h1' : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
      rcases h1' with (h | h | h | h | h)
      all_goals 
        simp [Int.mul_emod, Int.add_emod, h, Int.mul_emod, Int.add_emod]
    have h12 : (10 * x + 2) * (10 * x + 6) * (5 * x + 5) % 64 = 0 := by
      have h10 : x % 2 = 1 := h1 
      have h5 : x % 64 = 1 ∨ x % 64 = 3 ∨ x % 64 = 5 ∨ x % 64 = 7 ∨ x % 64 = 9 ∨ x % 64 = 11 ∨ x % 64 = 13 ∨ x % 64 = 15 ∨
            x % 64 = 17 ∨ x % 64 = 19 ∨ x % 64 = 21 ∨ x % 64 = 23 ∨ x % 64 = 25 ∨ x % 64 = 27 ∨ x % 64 = 29 ∨ x % 64 = 31 ∨
            x % 64 = 33 ∨ x % 64 = 35 ∨ x % 64 = 37 ∨ x % 64 = 39 ∨ x % 64 = 41 ∨ x % 64 = 43 ∨ x % 64 = 45 ∨ x % 64 = 47 ∨
            x % 64 = 49 ∨ x % 64 = 51 ∨ x % 64 = 53 ∨ x % 64 = 55 ∨ x % 64 = 57 ∨ x % 64 = 59 ∨ x % 64 = 61 ∨ x % 64 = 63 := by 
        omega
      rcases h5  with (h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5 |  h5) <;> simp [Int.mul_emod, Int.add_emod, h5, Int.mul_emod, Int.add_emod]
    omega 
  · -- Show 960 is the greatest such integer.
    intro y hy 
    have h3 : ∀ x : ℤ, Odd x → y ∣ (10 * x + 2) * (10 * x + 6) * (5 * x + 5) := hy 
    have h4 : y ∣ (10 * (1 : ℤ) + 2) * (10 * (1 : ℤ) + 6) * (5 * (1 : ℤ) + 5) := h3 1 (by decide)
    norm_num at h4
    have h5 : y ∣ (10 * (3 : ℤ) + 2) * (10 * (3 : ℤ) + 6) * (5 * (3 : ℤ) + 5) := h3 3 (by decide)
    norm_num at h5
    have h6 : y ∣ (10 * (5 : ℤ) + 2) * (10 * (5 : ℤ) + 6) * (5 * (5 : ℤ) + 5) := h3 5 (by decide)
    norm_num at h6 
    have h7 : y ∣ 960 := by 
      exact Int.dvd_gcd (Int.dvd_gcd h4 h5) h6 
    have h8 : y ≤ 960 := by 
      exact Int.le_of_dvd (by norm_num) h7 
    linarith