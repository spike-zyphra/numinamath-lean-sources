import Mathlib

theorem algebra_290008 :
  {m : ℝ | ∀ x : ℝ, m * x^2 + (m - 1) * x + m - 1 < 0} = 
  {m | m < -1/3} := by
  ext m 
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First direction: (∀ x, m * x ^ 2 + ... < 0): m < -1/3 
    intro h 
    have h1 := h 0
    have h2 := h 1 
    have h3 := h (-1)
    by_contra h4
    push_neg at h4
    have h7 : m ≠ 0 := by
      by_contra h8 
      have eq := h (-4)
      rw [h8] at eq
      norm_num at eq 
      all_goals linarith
    have eq := h (-2)
    have h5 : m < -1 / 3 := by
      nlinarith
    linarith [show m < ( -1 / 3 : ℝ ) by linarith] 
  · -- Back direction: m < -1/3: ∀ x, m * x ^ 2 + ... < 0
    intro h2 
    intro x 
    have h1 : m * x ^ 2 + (m - 1) * x + m - 1 < 0 := by 
      nlinarith [sq_nonneg (x * (m) + (m - 1) / 2), sq_nonneg (x + (m - 1) / (2 * m)), sq_pos_of_neg (show (m : ℝ) < 0 by linarith), sq_nonneg ((x) ^ 2 * (m) ), sq_nonneg ((x) ^ 2 * (m) ), sq_nonneg ((x) ) ]
    simpa using h1