import Mathlib

theorem algebra_94900 (total_people : ℕ) (h₀ : total_people > 0)
    (women : ℕ) (men : ℕ) (h₁ : women * 10 = men * 11) (h₂ : women + men = total_people)
    (age_women : ℝ) (age_men : ℝ) (h₃ : age_women = 34) (h₄ : age_men = 32) :
    (age_women * women + age_men * men) / total_people = 33 + 1 / 21 := by

  have eq1 : (age_women * (women : ℝ) + age_men * (men : ℝ)) = (34 * (women : ℝ) + 32 * (men : ℝ)) := by
    rw [h₃, h₄]

  have eq2 : (total_people : ℝ) = (women : ℝ) + (men : ℝ) := by
    have h6 : (women : ℝ) + (men : ℝ) = (total_people : ℝ) := by
      exact_mod_cast (show (women + men : ℕ) = (total_people : ℕ) by linarith [h₂])
    linarith

  have h7 : (women : ℝ) * 10 = (men : ℝ) * 11 := by 
    exact_mod_cast h₁

  have h9 : (total_people : ℝ) > 0 := by
    have h10 : (total_people : ℕ) > 0 := h₀
    have h11 : (total_people : ℝ) > 0 := by 
      exact_mod_cast h10 
    linarith

  have eq3 : ( (age_women * (women : ℝ) + age_men * (men : ℝ) ) / (total_people : ℝ) ) = (33 + 1 / 21 : ℝ) := by

    have h7 : (women : ℝ) * 10 = (men : ℝ) * 11 := h7

    have h6 : (men : ℕ) > 0 := by
      by_contra h
      push_neg at h
      have h8 : (men : ℕ) = 0 := by
        omega 
      have h9 : (men : ℝ) = (0 : ℝ) := by
        exact_mod_cast h8

      have hw0 : (women : ℝ) = (0 : ℝ) := by
        rw [h9] at h7
        linarith

      have hw : (women : ℕ) = 0 := by
        exact_mod_cast hw0

      have ht_zero : (total_people : ℕ) = 0 := by 
        have : (women : ℕ) + (men : ℕ) = (0 : ℕ) := by 
          omega 
        omega 

      have h18 : (total_people : ℕ) > 0 := h₀
      omega

    have eq4 : (women : ℝ) = (11 / 10) * (men : ℝ) := by
      linarith [h7]

    have eq5 : (total_people : ℝ) = (21 / 10) * ( (men : ℝ) ) := by 
      have eq5 : (women : ℝ) = (11 / 10) * (men : ℝ) := eq4
      linarith [eq5, eq2]

    have eq6 : (34 * (women : ℝ) + 32 * (men : ℝ)) / (total_people : ℝ) = (33 + 1 / 21 : ℝ) := by
      have eq5' : (total_people : ℝ) = (21 / 10) * ( (men : ℝ) ) := eq5
      have eq4' : (women : ℝ) = (11 / 10) * ( (men : ℝ) ) := eq4
      have h9 : ( (men : ℝ) ) > 0 := by
        have h8 : (men : ℕ) > 0 := h6
        have h9 : ( (men : ℝ) ) > 0 := by
          exact_mod_cast h8 
        linarith

      rw [eq4']
      rw [eq5']
      field_simp at *
      <;> nlinarith

    rw [eq1]
    exact_mod_cast eq6

  exact_mod_cast eq3