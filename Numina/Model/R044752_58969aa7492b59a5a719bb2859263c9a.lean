import Mathlib



theorem number_theory_286511 (total_people : ℕ) (h : total_people = 1240)
    (people_belief : ℕ) (people_not_belief : ℕ) (people_refuse : ℕ)(h1: people_belief + people_not_belief + people_refuse = total_people)
    (h_people_belief : people_belief = round ((46 / 100 : ℝ) * total_people))
    (h_people_not_belief : people_not_belief = round ((31 / 100 : ℝ) * total_people)) :
    people_belief ≥ 565 ∧ people_refuse ≤ 296 := by

  -- Substitute total_people = 1240 into the expressions
  rw [h] at h_people_belief h_people_not_belief

  have h1 : (people_belief : ℝ) = round ((46 / 100 : ℝ) * (1240 : ℝ)) := by exact_mod_cast h_people_belief
  have h2 : (people_not_belief : ℝ) = round ((31 / 100 : ℝ) * (1240 : ℝ)) := by exact_mod_cast h_people_not_belief

  have h3 : (people_belief : ℝ) = (570 : ℝ) := by
    rw [h1]
    norm_num [round_eq]
    all_goals linarith

  have h4 : (people_not_belief : ℝ) = (384 : ℝ) := by
    rw [h2]
    norm_num [round_eq]
    all_goals linarith

  have h5 : people_belief = 570 := by
    exact_mod_cast h3

  have h6 : people_not_belief = 384 := by
    exact_mod_cast h4

  -- Calculate people_refuse using the total sum constraint
  have h7 : people_refuse = 286 := by
    omega

  constructor
  · -- Show that people_belief ≥ 565
    omega
  · -- Show that people_refuse ≤ 296
    omega