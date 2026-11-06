import Mathlib

theorem logic_and_puzzles_95907 (u f : ℕ → ℕ)
    (hf1 : f 1 = 4) (hf2 : f 2 = 1)
    (hf3 : f 3 = 3) (hf4 : f 4 = 5) (hf5 : f 5 = 2)
    (hu0 : u 0 = 4) (hu : ∀ n, u (n+1) = f (u n)) : u 2002 = 2 := by

  have u1 : u 1 = 5 := by
    have h1 : u 1 = f (u 0) := hu 0
    rw [h1, hu0]
    simp [hf4]

  have u2 : u 2 = 2 := by
    have h2 : u 2 = f (u 1) := hu 1
    rw [h2, u1]
    simp [hf5]

  have u3 : u 3 = 1 := by
    have h3 : u 3 = f (u 2) := hu 2
    rw [h3, u2]
    simp [hf2]

  have u4 : u 4 = 4 := by
    have h4 : u 4 = f (u 3) := hu 3
    rw [h4, u3]
    simp [hf1]

  have cycle : ∀ (k : ℕ), u (4 * k) = 4 ∧ u (4 * k + 1) = 5 ∧ u (4 * k + 2) = 2 ∧ u (4 * k + 3) = 1 := by
    intro k 
    induction k with
    | zero =>
      constructor
      · exact hu0 
      constructor 
      · exact u1 
      constructor 
      · exact u2 
      · exact u3 
    | succ k ih =>
      have h4k4 : u (4 * (k + 1)) = 4 := by
        have eq1 : 4 * (k + 1) = 4 * k + 4 := by ring
        rw [eq1]
        have eq2 : u (4 * k + 4) = f (u (4 * k + 3)) := by 
          specialize hu (4 * k + 3)
          simpa using hu 
        rw [eq2]
        have h_u4k3 : u (4 * k + 3) = 1 := by
          omega 
        rw [h_u4k3] 
        simp [hf1]

      have h4k5 : u (4 * (k + 1) + 1) = 5 := by 
        have eq1 : 4 * (k + 1) + 1 = (4 * (k + 1)) + 1 := by ring 
        rw [eq1] 
        have eq2 : u ((4 * (k + 1)) + 1) = f (u (4 * (k + 1))) := by 
          specialize hu (4 * (k + 1))
          simpa using hu 
        rw [eq2] 
        rw [h4k4] 
        simp [hf4]

      have h4k6 : u (4 * (k + 1) + 2) = 2 := by 
        have eq1 : 4 * (k + 1) + 2 = (4 * (k + 1) + 1) + 1 := by ring 
        rw [eq1] 
        have eq2 : u ((4 * (k + 1) + 1) + 1) = f (u (4 * (k + 1) + 1)) := by 
          specialize hu (4 * (k + 1) + 1)
          simpa using hu 
        rw [eq2] 
        rw [h4k5] 
        simp [hf5]

      have h4k7 : u (4 * (k + 1) + 3) = 1 := by 
        have eq1 : 4 * (k + 1) + 3 = (4 * (k + 1) + 2) + 1 := by ring 
        rw [eq1] 
        have eq2 : u ((4 * (k + 1) + 2) + 1) = f (u (4 * (k + 1) + 2)) := by 
          specialize hu (4 * (k + 1) + 2)
          simpa using hu 
        rw [eq2] 
        rw [h4k6] 
        simp [hf2]

      constructor 
      · exact h4k4 
      constructor 
      · exact h4k5 
      constructor 
      · exact h4k6 
      · exact h4k7

  have h2002 : 4 * 500 + 2 = 2002 := by norm_num
  rw [show 2002 = 4 * 500 + 2 by norm_num]

  have h4k2 : u (4 * 500 + 2) = 2 := by
    have cycle_500 : u (4 * 500) = 4 ∧ u (4 * 500 + 1) = 5 ∧ u (4 * 500 + 2) = 2 ∧ u (4 * 500 + 3) = 1 := by
      apply cycle 500
    omega

  linarith [h4k2]