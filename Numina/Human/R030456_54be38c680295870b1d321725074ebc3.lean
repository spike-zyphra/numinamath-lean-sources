import Mathlib

/- Navin from Mauritius, Luka from Croatia, and Ian from Botswana are chatting in the lobby of a youth hostel discussing their part-time jobs. They learn that Navin makes 160 rupee per hour, Luka makes 25 kuna per hour, and Ian makes 34 pula per hour. If one US dollar is equivalent to 32.35 Mauritius rupee, 5.18 Croatian kuna, and 6.95 Botswana pula, who would earn the most after working an eight-hour day? -/
theorem algebra_21264 (Navin Luka Ian rupee kuna pula dollar : ℝ) (h1 : Navin = 160 * rupee) (h2 : Luka = 25 * kuna) (h3 : Ian = 34 * pula) (h4 : 0 < dollar) (h5 : dollar = 32.35 * rupee) (h6 : dollar = 5.18 * kuna) (h7 : dollar = 6.95 * pula) : IsGreatest {8 * Navin, 8 * Luka, 8 * Ian} (8 * Navin) := by
  constructor
  simp only [Set.mem_insert_iff, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, Set.mem_singleton_iff, true_or]
  -- Navin would earn the most by some computation, 
  norm_num at h5
  norm_num at h6
  norm_num at h7
  intro x xin
  rcases xin with xeq | xeq | xeq
  linarith
  linarith
  rw [Set.mem_singleton_iff] at xeq
  linarith