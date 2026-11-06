import Mathlib

/-A super ball is dropped from 100 feet and rebounds half the distance it falls each time it bounces. How many feet will the ball have traveled when it hits the ground the fourth time?-/
theorem algebra_11912 {f : ℕ → ℝ} (f0 : f 0 = 100) (h' : ∀ i : ℕ, f (i + 1) = f i / 2) :
    ∑ i ∈ Finset.range 4, f i + ∑ i ∈ Finset.range 3, (1/2) * f i = 275 := by
  -- The ball traveled $100+50+25+12.5 = 187.5$ feet on its four descents. The ball also traveled $50+25+12.5 = 87.5$ feet on its three ascents. Thus, the ball traveled $187.5+87.5 = \boxed{275}$ feet total.
  have f1: f 1 = 50 := by
    specialize h' 0
    linarith
  have f2: f 2 = 25 := by
    specialize h' 1
    linarith
  have f3: f 3 = 12.5 := by
    specialize h' 2
    rw [f2] at h'
    simp at h'
    rw [h']
    norm_num
  rw [(Finset.mul_sum _ _ _).symm, Finset.range_succ]
  simp
  have : ∑ i ∈ Finset.range 3, f i = 175 := by
    have : Finset.range 3 = {0, 1, 2} := by rfl
    rw [this]
    simp
    linarith
  rw [this, f3]
  norm_num
