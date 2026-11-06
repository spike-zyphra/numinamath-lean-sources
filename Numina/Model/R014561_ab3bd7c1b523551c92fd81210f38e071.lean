import Mathlib

theorem number_theory_5997
(a b : ℕ)
(ρ : ℝ)
(h₀ : 0 < a)
(h₁ : 0 < b)
(h₂ : Nat.gcd a b = 1)
(h₃ : ∃ m n : ℤ, a * ρ = m ∧ b * ρ = n)
: ∃ p : ℤ, ρ = p := by
  rcases h₃ with ⟨m, n, h₃₁, h₃₂⟩
  have eq1 : (a : ℝ) * ρ = (m : ℝ) := by
    simpa using h₃₁
  have eq2 : (b : ℝ) * ρ = (n : ℝ) := by
    simpa using h₃₂
  have eq3 : (m : ℝ) * (b : ℝ) = (n : ℝ) * (a : ℝ) := by
    have eq4 : (a : ℝ) * ρ = (m : ℝ) := eq1
    have eq5 : (b : ℝ) * ρ = (n : ℝ) := eq2
    have eq10 : (a : ℝ) * (b : ℝ) * ρ = (m : ℝ) * (b : ℝ) := by
      calc
        (a : ℝ) * (b : ℝ) * ρ = (a * ρ) * (b : ℝ) := by ring
        _ = (m : ℝ) * (b : ℝ) := by rw [eq4]
    have eq11 : (a : ℝ) * (b : ℝ) * ρ = (a : ℝ) * (n : ℝ) := by
      calc
        (a : ℝ) * (b : ℝ) * ρ = (a : ℝ) * (b * ρ) := by ring
        _ = (a : ℝ) * (n : ℝ) := by rw [eq5]
    have eq12 : (a : ℝ) * (n : ℝ) = (n : ℝ) * (a : ℝ) := by
      ring
    linarith [eq10, eq11, eq12]
  have eq4 : m * b = n * a := by
    have eq5 : (m : ℝ) * (b : ℝ) = (n : ℝ) * (a : ℝ) := eq3
    norm_cast at eq5 ⊢
  have h4 : m * b = n * a := eq4
  have h5 : Nat.Coprime a b := by
    rw [Nat.coprime_iff_gcd_eq_one]
    exact_mod_cast h₂
  have eq6' : (m : ℤ) * (b : ℤ) = (n : ℤ) * (a : ℤ) := by
    norm_cast at eq4 ⊢
  have eq7' : IsCoprime (a : ℤ) (b : ℤ) := by
    rw [Int.coprime_iff_nat_coprime]
    exact_mod_cast h5
  have h6 : (a : ℤ) ∣ (m : ℤ) * (b : ℤ) := by
    use n
    linarith [eq6']
  have h7 : (a : ℤ) ∣ (m : ℤ) := by
    apply IsCoprime.dvd_of_dvd_mul_right eq7' h6
  rcases h7 with ⟨l, hl⟩
  have eq9 : (a : ℝ) * ρ = (l : ℝ) * (a : ℝ) := by
    have eq10 : (a : ℝ) * ρ = (m : ℝ) := eq1
    have eq11 : (m : ℝ) = (l : ℝ) * (a : ℝ) := by
      have eq12 : (m : ℤ) = l * (a : ℤ) := by
        linarith [hl]
      norm_cast at eq12 ⊢
      all_goals linarith
    rw [eq11] at eq10
    linarith
  have eq10 : ρ = (l : ℝ) := by
    have eq11 : (a : ℝ) > 0 := by
      exact_mod_cast (show (0 : ℕ) < a by linarith)
    have eq12 : (a : ℝ) * ρ = (l : ℝ) * (a : ℝ) := eq9
    have eq13 : (a : ℝ) * (ρ - (l : ℝ)) = 0 := by
      linarith
    have eq14 : ρ - (l : ℝ) = 0 := by
      apply (mul_left_inj' (ne_of_gt eq11)).mp 
      linarith 
    linarith 
  exact ⟨l, by linarith [eq10]⟩