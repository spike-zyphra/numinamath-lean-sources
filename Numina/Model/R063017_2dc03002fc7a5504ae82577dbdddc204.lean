import Mathlib

theorem number_theory_218410 {x y z : ℕ} (h : x^2 + y^2 = z^2) :
    3 ∣ x ∨ 3 ∣ y ∨ 3 ∣ z := by
  by_contra h1
  push_neg at h1

  have h2 : x % 3 = 1 ∨ x % 3 = 2 := by 
    omega

  have h3 : y % 3 = 1 ∨ y % 3 = 2 := by 
    omega

  have h4 : z % 3 = 1 ∨ z % 3 = 2 := by 
    omega

  have hx2 : x^2 % 3 = 1 := by
    rcases h2 with (h2 | h2)
    · -- x ≡ 1 (mod 3)
      norm_num [Nat.pow_mod, h2]
    · -- x ≡ 2 (mod 3)
      norm_num [Nat.pow_mod, h2]

  have hy2 : y^2 % 3 = 1 := by 
    rcases h3 with (h3 | h3)
    · -- y ≡ 1 (mod 3)
      norm_num [Nat.pow_mod, h3]
    · -- y ≡ 2 (mod 3)
      norm_num [Nat.pow_mod, h3]

  have hz2 : z^2 % 3 = 1 := by 
    rcases h4 with (h4 | h4)
    · -- z ≡ 1 (mod 3)
      norm_num [Nat.pow_mod, h4]
    · -- z ≡ 2 (mod 3)
      norm_num [Nat.pow_mod, h4]

  have h5 : (x^2 + y^2) % 3 = 2 := by
    omega

  have h6 : (x^2 + y^2) % 3 = z^2 % 3 := by 
    omega

  omega