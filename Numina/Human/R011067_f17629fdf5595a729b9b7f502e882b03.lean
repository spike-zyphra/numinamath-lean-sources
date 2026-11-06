import Mathlib

/- Task 4. (20 points) To get from the first to the second building of the university, Sasha took a car-sharing vehicle, while Valya rented a scooter. Sasha and Valya set off from the first building to the second at the same time, and at the same time, teacher Sergei Vladimirovich set off from the second building to the first in a car. The cars met after 4 minutes, and the scooter and the teacher's car met 1 km from the main building. Find the speeds of the cars and the scooter, if the scooter takes 1.4 hours longer to cover a distance of 18 km compared to the car-sharing vehicle, and its speed is 6 times less than the speed of Sergei Vladimirovich's car. In your answer, indicate the speeds in $\frac{\kappa M}{\psi}$ in ascending order. -/
theorem algebra_214829 (v_s v_t v_v d : ℝ) (h_v : v_s > 0 ∧ v_t > 0 ∧ v_v > 0) (hd : d > 0)
    (h_s_t_meet : v_s * (4 / 60) + v_t * (4 / 60) = d) (h_v_t_meet : 1 / v_v = (d - 1) / v_t )
    (h_v_s_speed : 18 / v_v = 18 / v_s + 1.4) (h_v_t_speed : v_t = 6 * v_v) :
    v_v = 10 ∧ v_s = 45 ∧ v_t = 60 := by
  -- v_s is sasha's speed, v_t is teacher's speed, v_v is valya's speed, d is distance between two buildings
  -- times are in hour and distances in km
  obtain ⟨h_v_s, h_v_t, h_v_v⟩ := h_v
  -- first we write v_t in terms of v_v and compute d to be 7
  rw [h_v_t_speed] at h_v_t_meet
  field_simp at h_v_t_meet
  have hd : d = 7 := by linarith
  rw [hd] at h_s_t_meet
  clear hd h_v_t_meet
  clear hd
  -- now write v_s in terms of v_v
  replace h_s_t_meet : v_s = 105 - 6 * v_v := by linarith
  field_simp at h_v_s_speed
  -- so everything can be written in terms of v_v, we get a quadratic equation
  rw [h_s_t_meet] at h_v_s_speed
  ring_nf at h_v_s_speed
  -- the equation factorizes to following, right factor can't be 0 as that'd make v_s negative
  replace h_v_s_speed : (v_v - 10) * (42 * v_v - 945) = 0 := by linarith
  have : 42 * v_v - 945 ≠ 0 := by linarith
  -- so we get v_v and all the values
  simp [this] at h_v_s_speed
  and_intros <;> linarith