import Mathlib

theorem algebra_114910 {a b c d : ℝ}
    (h : ∀ x ∈ Set.Icc (-1 : ℤ) 2, ∃ n : ℤ, a * x^3 + b * x^2 + c * x + d = n) :
    ∀ x : ℤ, ∃ n : ℤ, a * x^3 + b * x^2 + c * x + d = n := by

  have h1 := h (-1) (by norm_num)
  rcases h1 with ⟨n1, hn1⟩

  have h2 := h (0 : ℤ) (by norm_num)
  rcases h2 with ⟨n2, hn2⟩

  have h3 := h (1 : ℤ) (by norm_num)
  rcases h3 with ⟨n3, hn3⟩

  have h4 := h (2 : ℤ) (by norm_num)
  rcases h4 with ⟨n4, hn4⟩

  intro x

  have eq1 : a * (-1 : ℤ)^3 + b * (-1 : ℤ)^2 + c * (-1 : ℤ) + d = (n1 : ℝ) := by
    simpa using hn1

  have eq2 : a * (0 : ℤ)^3 + b * (0 : ℤ)^2 + c * (0 : ℤ) + d = (n2 : ℝ) := by
    simpa using hn2

  have eq3 : a * (1 : ℤ)^3 + b * (1 : ℤ)^2 + c * (1 : ℤ) + d = (n3 : ℝ) := by
    simpa using hn3

  have eq4 : a * (2 : ℤ)^3 + b * (2 : ℤ)^2 + c * (2 : ℤ) + d = (n4 : ℝ) := by
    simpa using hn4

  have h_eq2 : d = (n2 : ℝ) := by
    norm_num at eq2
    linarith

  have eq1' : -a + b - c + (n2 : ℝ) = (n1 : ℝ) := by
    norm_num at eq1
    linarith [h_eq2, eq1]

  have eq3' : a + b + c + (n2 : ℝ) = (n3 : ℝ) := by
    norm_num at eq3
    linarith [h_eq2, eq3]

  have eq4' : 8 * a + 4 * b + 2 * c + (n2 : ℝ) = (n4 : ℝ) := by
    norm_num at eq4
    linarith [h_eq2, eq4]

  have eq5 : a = (n4 - 3 * n3 - n1 + 3 * n2 : ℝ) / 6 := by
    nlinarith

  have eq6 : c = (6 * n3 - (n4 + 2 * n1 + 3 * n2) : ℝ) / 6 := by
    nlinarith [eq5]

  have eq7 : b = (n1 + n3 - 2 * n2 : ℝ) / 2 := by
    nlinarith [eq3']

  have eq9 : ∃ n : ℤ, a * x^3 + b * x^2 + c * x + d = n := by
    have eq14 : a * (x : ℝ)^3 + b * (x : ℝ)^2 + c * (x : ℝ) + d =
        (( (n4 - 3 * n3 - n1 + 3 * n2 ) * x^3 + 3 * (n1 + n3 - 2 * n2 ) * x^2 + (6 * n3 - (n4 + 2 * n1 + 3 * n2 ) ) * x + 6 * n2 ) / (6 : ℝ)) := by
      rw [show a = (n4 - 3 * n3 - n1 + 3 * n2 : ℝ) / 6 by linarith [eq5], 
          show b = (n1 + n3 - 2 * n2 : ℝ) / 2 by linarith [eq7], 
          show c = (6 * n3 - (n4 + 2 * n1 + 3 * n2) : ℝ) / 6 by linarith [eq6], 
          show d = (n2 : ℝ) by linarith [h_eq2]]
      field_simp
      ring_nf

    rw [eq14]

    have eq17 : ∃ k : ℤ, ( (n4 - 3 * n3 - n1 + 3 * n2 ) * x^3 + 3 * (n1 + n3 - 2 * n2 ) * x^2 + (6 * n3 - (n4 + 2 * n1 + 3 * n2 ) ) * x + 6 * n2 ) = 6 * k := by
      have h1 : ( (n4 - 3 * n3 - n1 + 3 * n2 ) * x^3 + 3 * (n1 + n3 - 2 * n2 ) * x^2 + (6 * n3 - (n4 + 2 * n1 + 3 * n2 ) ) * x + 6 * n2 ) % (6 : ℤ) = 0 := by
        have h2 : ( (n4 - 3 * n3 - n1 + 3 * n2 ) * x^3 + 3 * (n1 + n3 - 2 * n2 ) * x^2 + (6 * n3 - (n4 + 2 * n1 + 3 * n2 ) ) * x + 6 * n2 ) % (2 : ℤ) = 0 := by
          have h1 : x % 2 = 0 ∨ x % 2 = 1 := by omega
          rcases h1 with (h1 | h1)
          · -- x ≡ 0 (mod 2)
            simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h1, Int.ofNat]
            all_goals omega
          · -- x ≡ 1 (mod 2)
            simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h1, Int.ofNat]
            all_goals omega

        have h3 : ( (n4 - 3 * n3 - n1 + 3 * n2 ) * x^3 + 3 * (n1 + n3 - 2 * n2 ) * x^2 + (6 * n3 - (n4 + 2 * n1 + 3 * n2 ) ) * x + 6 * n2 ) % (3 : ℤ) = 0 := by
          have h4 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
          rcases h4 with (h4 | h4 | h4)
          · -- x ≡ 0 (mod 3)
            simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4, Int.ofNat]
            all_goals omega
          · -- x ≡ 1 (mod 3)
            simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4, Int.ofNat]
            all_goals omega
          · -- x ≡ 2 (mod 3)
            simp [Int.add_emod, Int.mul_emod, pow_two, pow_succ, h4, Int.ofNat]
            all_goals omega

        omega

      refine' ⟨ ( (n4 - 3 * n3 - n1 + 3 * n2 ) * x^3 + 3 * (n1 + n3 - 2 * n2 ) * x^2 + (6 * n3 - (n4 + 2 * n1 + 3 * n2 ) ) * x + 6 * n2 ) / 6, by omega ⟩

    rcases eq17 with ⟨k, hk⟩

    use k

    have eq18 : (( (n4 - 3 * n3 - n1 + 3 * n2 ) * x^3 + 3 * (n1 + n3 - 2 * n2 ) * x^2 + (6 * n3 - (n4 + 2 * n1 + 3 * n2 ) ) * x + 6 * n2 ) / (6 : ℝ)) = (k : ℝ) := by
      have eq19 : ( (n4 - 3 * n3 - n1 + 3 * n2 ) * x^3 + 3 * (n1 + n3 - 2 * n2 ) * x^2 + (6 * n3 - (n4 + 2 * n1 + 3 * n2 ) ) * x + 6 * n2 : ℝ) = (6 * (k : ℝ) ) := by
        exact_mod_cast show ( (n4 - 3 * n3 - n1 + 3 * n2 ) * x^3 + 3 * (n1 + n3 - 2 * n2 ) * x^2 + (6 * n3 - (n4 + 2 * n1 + 3 * n2 ) ) * x + 6 * n2 ) = (6 * k : ℤ) by linarith [hk]
      have eq20 : ( (n4 - 3 * n3 - n1 + 3 * n2 ) * x^3 + 3 * (n1 + n3 - 2 * n2 ) * x^2 + (6 * n3 - (n4 + 2 * n1 + 3 * n2 ) ) * x + 6 * n2 : ℝ) = (6 * (k : ℝ) ) := by
        linarith
      field_simp at eq20 ⊢
      linarith

    linarith [eq18]

  simpa using eq9