import Mathlib

theorem number_theory_144191 {x y : ℤ} (h₀ : x / y = 2 ∧ x % y = 2) (h₁ : (x + y) / (x - y) = 2 ∧ (x + y) % (x - y) = 8) :
    x.gcd y = 2 ∧ x.lcm y = 110 := by

  rcases h₀ with ⟨h₀1, h₀2⟩
  rcases h₁ with ⟨h₁1, h₁2⟩

  have h2 : x = 2 * y + 2 := by 
    rw [← Int.ediv_add_emod x y, h₀1, h₀2]
    all_goals -- To derive the equation from division with remainder
      omega
  have h3 : x - y ≠ 0 := by 
      by_contra h
      have : (x + y) / (x - y) = 0 := by
        rw [h]
        norm_num
        all_goals omega
      linarith
  have h4 : x + y = 2 * (x - y) + 8 := by 
    rw [← Int.ediv_add_emod (x + y) (x - y), h₁1, h₁2]
    all_goals -- To derive the equation from division with remainder
      omega
  have h5 : y = 10 := by 
    nlinarith [h2, h4]
  have h6 : x = 22 := by 
    rw [h5] at h2 
    linarith 
  have h7 : x.gcd y = 2 := by 
    rw [show x = 22 by linarith, show y = 10 by linarith]
    norm_num
  have h8 : x.lcm y = 110 := by 
    rw [show x = 22 by linarith, show y = 10 by linarith]
    norm_num [Int.lcm]
  exact ⟨h7, h8⟩