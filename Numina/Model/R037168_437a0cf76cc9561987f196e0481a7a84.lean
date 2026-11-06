import Mathlib

theorem algebra_126801 {a : ℝ} (ha : abs a = -a) :
    -(abs (a - 1) - abs (2 - a)) = 1 := by
  have h1 : a ≤ 0 := by
    cases' abs_cases a with ha1 ha1
    · linarith
    · linarith

  have h2 : abs (a - 1) = - (a - 1) := by
    rw [abs_of_nonpos]
    · linarith
    all_goals linarith

  have h3 : abs (2 - a) = 2 - a := by 
    rw [abs_of_nonneg]
    · linarith
    all_goals linarith

  calc
    -(abs (a - 1) - abs (2 - a)) = - ((- (a - 1)) - (2 - a)) := by 
      rw [h2, h3]
    _ = - ((-a + 1) - (2 - a)) := by ring_nf
    _ = - (-1) := by
      have h5 : (-a + 1) - (2 - a) = -1 := by linarith 
      rw [h5]
    _ = 1 := by norm_num