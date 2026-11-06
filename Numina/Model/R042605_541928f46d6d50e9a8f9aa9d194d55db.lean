import Mathlib.Tactic

theorem alg_1187
  (t w : ℝ)
  (r₁ r₂ r : ℚ)
  (doug_rate : r₁ = 1 / 5)
  (dave_rate : r₂ = 1 / 7)
  (combined_rate : r = r₁ + r₂)
  (total_work_time : w = t - 1) :
  r * w = 1 ↔ t = 47 / 12 := by
  constructor
  · -- Assume r * w = 1, need to prove t = 47 / 12
    intro h
    rw [combined_rate, total_work_time] at h
    rw [doug_rate, dave_rate] at h
    norm_num at h
    have ht : (t : ℝ) = 47 / 12 := by
      linarith
    exact_mod_cast ht
  · -- Assume t = 47 / 12, need to prove r * w = 1
    intro h
    rw [combined_rate, total_work_time]
    rw [doug_rate, dave_rate]
    rw [h]
    norm_num