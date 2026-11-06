import Mathlib

theorem number_theory_254602 {n : ℤ} (hn : Odd n) (h3 : ¬ 3 ∣ n) :
    6 ∣ n^2 + 5 := by
  have h1 : n % 2 = 1 := by
    rcases hn with ⟨k, hk⟩
    omega

  have h2 : n % 3 = 1 ∨ n % 3 = 2 := by 
    omega

  have h8 : n % 6 = 1 ∨ n % 6 = 5 := by 
    omega

  rcases h8 with (h | h)

  · -- Case n ≡ 1 (mod 6)
    have h10 : (n ^ 2 + 5) % 6 = 0 := by 
      have h9 : n % 6 = 1 := h
      have h11 : n ^ 2 % 6 = 1 := by
        have h12 : n % 6 = 1 := h9
        norm_num [pow_two, Int.add_emod, Int.mul_emod, h12]
      omega
    exact Int.dvd_of_emod_eq_zero h10

  · -- Case n ≡ 5 (mod 6)
    have h11 : (n ^ 2 + 5) % 6 = 0 := by 
      have h12 : n % 6 = 5 := h
      have h13 : n ^ 2 % 6 = 1 := by 
        have h9 : n % 6 = 5 := h12
        norm_num [pow_two, Int.add_emod, Int.mul_emod, h9]
      omega
    exact Int.dvd_of_emod_eq_zero h11