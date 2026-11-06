import Mathlib

theorem number_theory_286511 (total_people : ℕ) (h : total_people = 1240)
    (people_belief : ℕ) (people_not_belief : ℕ) (people_refuse : ℕ)(h1: people_belief + people_not_belief + people_refuse = total_people)
    (h_people_belief : people_belief = round ((46 / 100 : ℝ) * total_people))
    (h_people_not_belief : people_not_belief = round ((31 / 100 : ℝ) * total_people)) :
    people_belief ≥ 565 ∧ people_refuse ≤ 296 := by
  rw [h] at h_people_belief h_people_not_belief
  have h1 : (people_belief : ℝ) = round ((46 / 100 : ℝ) * (1240 : ℕ)) := by
    exact_mod_cast h_people_belief
  have h2 : (people_not_belief : ℝ) = round ((31 / 100 : ℝ) * (1240 : ℕ)) := by
    exact_mod_cast h_people_not_belief
  have h3 : (people_belief : ℝ) = 570 := by
    rw [h1]
    norm_num [round_eq]
  have h4 : (people_not_belief : ℝ) = 384 := by
    rw [h2]
    norm_num [round_eq]
  have h5 : people_belief = 570 := by
    exact_mod_cast h3
  have h6 : people_not_belief = 384 := by
    exact_mod_cast h4
  constructor
  · -- Prove people_belief ≥ 565
    omega
  · -- Prove people_refuse ≤ 296
    omega