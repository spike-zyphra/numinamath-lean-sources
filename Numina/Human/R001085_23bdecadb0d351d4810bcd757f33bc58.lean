import Mathlib

/- Each good worker can paint my new house alone in 12 hours.  Each bad worker can paint my house alone in 36 hours.  I need my house painted in 3 hours.  If I can only find 3 good workers, how many bad workers must I also find in order to have my house painted on time? -/
theorem algebra_20391 (num_good_worker num_bad_worker time_good_worker time_bad_worker needed_time : ℕ) (h1 : time_good_worker = 12) (h2 : time_bad_worker = 36) (h3 : needed_time = 3) (h4 : (num_good_worker : ℚ) * (1 / time_good_worker) + num_bad_worker * (1 / time_bad_worker) = 1 / (needed_time)) (h5 : num_good_worker = 3) :
    num_bad_worker = 3 := by
  -- Substitute num_good_worker = 3 into the equation
  rw [h1, h2, h3, h5] at h4
  -- Simplify the equation
  norm_num at h4
  -- Multiply both sides by 36 to clear the denominators
  have h5 : (9 : ℚ) + num_bad_worker = 12 := by
    have : ((1 : ℚ) / 4 + ↑num_bad_worker * (1 / 36)) * 36 = 1 / 3 * 36 := by
      rw [h4]
    ring_nf at this
    exact this
  -- Solve for num_bad_worker
  rw [add_comm] at h5
  apply eq_sub_of_add_eq at h5
  ring_nf at h5
  exact Rat.natCast_inj.mp h5