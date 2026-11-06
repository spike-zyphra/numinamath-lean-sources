import Mathlib

theorem number_theory_195007 :
    {(x, y) : ℕ × ℕ | x^2 + 1001 = y^2}.encard = 4 := by
  have h1 : {(x, y) : ℕ × ℕ | x^2 + 1001 = y^2} = {(32, 45), (40, 51), (68, 75), (500, 501)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume x^2 + 1001 = y^2, prove (x,y) ∈ {(32,45), (40,51), (68,75), (500,501)}
      rintro H
      have h2 : y^2 = x^2 + 1001 := by linarith
      have h3 : y > x := by
        by_contra h
        push_neg at h
        have h4 : y ≤ x := by linarith
        have h5 : y^2 ≤ x^2 := by nlinarith
        nlinarith
      have h2' : (y : ℤ)^2 = (x : ℤ)^2 + 1001 := by
        exact_mod_cast (show y^2 = x^2 + 1001 by linarith)
      have h3' : ((y : ℤ) - (x : ℤ)) * ((y : ℤ) + (x : ℤ)) = 1001 := by
        nlinarith
      have h4 : (y : ℤ) > (x : ℤ) := by exact_mod_cast h3
      have h5 : ((y : ℤ) - (x : ℤ)) > 0 := by nlinarith
      have h6 : ((y : ℤ) + (x : ℤ)) > 0 := by nlinarith
      have h7 : ((y : ℤ) - (x : ℤ)) ∣ 1001 := by
        use ((y : ℤ) + (x : ℤ))
        all_goals
          linarith [h3']
      have h8 : ((y : ℤ) - (x : ℤ)) ≤ 1001 := by
        exact Int.le_of_dvd (show 0 < 1001 by norm_num) h7
      have h10 : ((y : ℤ) - (x : ℤ)) ≥ 1 := by nlinarith
      interval_cases h11 : ((y : ℤ) - (x : ℤ)) <;> omega
    · -- Assume (x,y) ∈ {(32,45), (40,51), (68,75), (500,501)}, prove x^2 + 1001 = y^2
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]