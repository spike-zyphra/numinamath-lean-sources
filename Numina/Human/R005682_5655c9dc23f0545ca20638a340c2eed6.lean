import Mathlib

/-
Theorem: The number of distinct non-congruent triangles formed by three vertices of a regular decagon is 8. This is equivalent to counting the number of unordered partitions of 10 into three positive integers.
-/
theorem my_favorite_theorem :
    {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = 10}.ncard = 8 := by

  -- Define S as the set of triples (x,y,z) that are positive integers, non-decreasing, and sum to 10
  let S := {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = 10}

  -- Prove that S is equal to the set defined by the same conditions
  have S₁ : S={(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = 10 } :=by exact
    rfl

  -- Prove that S is equal to the explicit list of 8 triples
  have h : S = {(1 , 1 , 8) , (1 , 2 , 7) , (1 , 3 , 6) , (1 , 4 , 5) , (2 , 2 , 6) , (2 , 3 , 5) , (2 , 4 , 4) , (3 , 3 , 4)} := by

    -- Prove equality by extensionality (showing membership in both directions)
    ext ⟨x, y, z⟩
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro h

      -- Destructure the hypothesis into individual conditions
      rcases h with ⟨hx , hy , hz , hxy , hyz , hsum⟩
      
      -- Show that x must be less than or equal to 3
      have hx_le_3 : x ≤ 3 := by linarith [hxy, hyz, hsum]

      -- Case analysis on possible values of x
      interval_cases x
      · 
        -- For x=1, y must be less than or equal to 4
        have hy_le_4 : y ≤ 4 := by linarith [hxy, hyz, hsum]

        -- Case analysis on possible values of y when x=1
        interval_cases y
        · 
          have z := by exact x
          simp [hxy, hyz, hsum]
          exact Nat.add_left_cancel hsum
        · 
          have z := by exact x
          simp [hxy, hyz, hsum]
          exact Nat.add_left_cancel hsum
        · 
          have z := by exact x
          simp [hxy, hyz, hsum]
          exact Nat.add_left_cancel hsum
        · 
          have z := by exact x
          simp [hxy, hyz, hsum]
          exact Nat.add_left_cancel hsum
      · 
        -- For x=2, y must be less than or equal to 4
        have hy_le_4 : y ≤ 4 := by linarith [hxy, hyz, hsum]
        
        -- Case analysis on possible values of y when x=2
        interval_cases y
        · 
          have z := by exact x
          simp [hxy, hyz, hsum]
          exact Nat.add_left_cancel hsum
        · 
          have z := by exact x
          simp [hxy, hyz, hsum]
          exact Nat.add_left_cancel hsum
        · 
          have z := by exact x
          simp [hxy, hyz, hsum]
          exact Nat.add_left_cancel hsum
      · 
        -- For x=3, y must be less than or equal to 3
        have hy_le_3 : y ≤ 3 := by linarith [hxy, hyz, hsum]

        -- Case analysis on possible values of y when x=3
        interval_cases y
        · 
          have z := by exact x
          simp [hxy, hyz, hsum]
          exact Nat.add_left_cancel hsum
    · 
      -- Prove that each of the 8 explicit triples is in S
      rintro (⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩)  
      all_goals
      aesop

  -- Rewrite the set equality in the original statement
  rw [h] at S₁
  rw[← S₁]
  norm_num