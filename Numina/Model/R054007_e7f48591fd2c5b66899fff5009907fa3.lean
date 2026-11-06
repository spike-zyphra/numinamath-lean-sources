import Mathlib

theorem number_theory_107960 (a b c : ℕ) (h₀ : a + b + c = 100)
    (h₁ : |(a : ℤ) - b| = 60) (h₂ : |(a : ℤ) - c| = 38) :
    a = 66 ∧ b = 6 ∧ c = 28 := by
  have h3 : (a : ℤ) + (b : ℤ) + (c : ℤ) = 100 := by
    norm_num
    omega
  have h4 : (a : ℤ) - b = 60 ∨ (a : ℤ) - b = -60 := by
    simpa [abs_eq] using h₁
  have h5 : (a : ℤ) - c = 38 ∨ (a : ℤ) - c = -38 := by
    simpa [abs_eq] using h₂
  rcases h4 with h4 | h4
  · -- Case where (a : ℤ) - b = 60
    rcases h5 with h5 | h5
    · -- Case where (a : ℤ) - c = 38
      have ha : (a : ℤ) = (b : ℤ) + 60 := by linarith
      have ha2 : (a : ℤ) = (c : ℤ) + 38 := by linarith
      have hb : (b : ℤ) = (c : ℤ) - 22 := by linarith
      have h6 : (a : ℤ) + (b : ℤ) + (c : ℤ) = 100 := by
        norm_num
        omega
      have hc : (c : ℤ) = 28 := by
        nlinarith
      have hb2 : (b : ℤ) = 6 := by
        linarith
      have ha3 : (a : ℤ) = 66 := by
        linarith
      have ha4 : a = 66 := by
        norm_num at ha3 ⊢
        exact_mod_cast ha3
      have hb3 : b = 6 := by
        norm_num at hb2 ⊢
        exact_mod_cast hb2
      have hc2 : c = 28 := by
        norm_num at hc ⊢
        exact_mod_cast hc
      exact ⟨ha4, hb3, hc2⟩
    · -- Case where (a : ℤ) - c = -38
      have ha : (a : ℤ) = (b : ℤ) + 60 := by linarith
      have hc : (c : ℤ) = (a : ℤ) + 38 := by linarith
      have h6 : (a : ℤ) + (b : ℤ) + (c : ℤ) = 100 := by
        norm_num
        omega
      omega
  · -- Case where (a : ℤ) - b = -60
    rcases h5 with h5 | h5
    · -- Case where (a : ℤ) - c = 38
      have hb : (b : ℤ) = (a : ℤ) + 60 := by linarith
      have ha2 : (a : ℤ) = (c : ℤ) + 38 := by linarith
      have h6 : (a : ℤ) + (b : ℤ) + (c : ℤ) = 100 := by
        norm_num
        omega
      omega
    · -- Case where (a : ℤ) - c = -38
      have hb : (b : ℤ) = (a : ℤ) + 60 := by linarith
      have hc : (c : ℤ) = (a : ℤ) + 38 := by linarith
      have h6 : (a : ℤ) + (b : ℤ) + (c : ℤ) = 100 := by
        norm_num
        omega
      omega