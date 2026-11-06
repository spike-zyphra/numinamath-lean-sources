import Mathlib

theorem number_theory_323122 (a : ℕ) (ha : a > 0) (h : a ≡ 3 [ZMOD 4]) :
    ¬∃ x y : ℤ, x^2 + y^2 = a := by
  intro h1
  rcases h1 with ⟨x, y, h_eq⟩
  have h2 : (x ^ 2 + y ^ 2 : ℤ) % 4 = 0 ∨ (x ^ 2 + y ^ 2 : ℤ) % 4 = 1 ∨ (x ^ 2 + y ^ 2 : ℤ) % 4 = 2 := by
    have h3 : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
      have h1 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by
        omega
      rcases h1 with (h | h | h | h) <;> norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at *
    have h4 : y ^ 2 % 4 = 0 ∨ y ^ 2 % 4 = 1 := by
      have h2 : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by
        omega
      rcases h2 with (h | h | h | h) <;> norm_num [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at *
    omega
  have h3 : (a : ℤ) % 4 = 3 := by
    norm_num [Int.ModEq] at h
    exact_mod_cast h
  have h4 : (x ^ 2 + y ^ 2 : ℤ) = (a : ℤ) := by
    linarith [h_eq]
  have h5 : (a : ℤ) % 4 = 3 := h3
  have h6 : (x ^ 2 + y ^ 2 : ℤ) % 4 = (a : ℤ) % 4 := by
    omega
  omega