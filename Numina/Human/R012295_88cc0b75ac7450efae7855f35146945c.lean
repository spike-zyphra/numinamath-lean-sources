import Mathlib

set_option maxHeartbeats 8000000

-- we first prove a simple identity
lemma lemma_1 (x y z: ℕ): x * y * z + x * y + y * z + z * x + x + y + z + 1 = (x + 1) * (y + 1) * (z + 1) := by
  ring

/-How many triples of non-negative integers 
(x,y,z) satisfying the equation
x * y * z + x * y + y * z + z * x + x + y + z = 2012-/

theorem number_theory_101075: {(x, y, z): ℕ × ℕ × ℕ | x * y * z + x * y + y * z + z * x + x + y + z = 2012}.encard = 27 := by

  -- we directly compute the set
  have h_eq: {(x, y, z): ℕ × ℕ × ℕ | x * y * z + x * y + y * z + z * x + x + y + z = 2012} =  
  {(0,2012,0), (2012,0,0), (0,0,2012),(0,2,670), (0,670,2), (2,0,670), (2,670,0), (670,0,2), (670,2,0),
  (0,10,182), (0,182,10), (10,0,182), (10,182,0), (182,0,10), (182,10,0),
  (0,32,60), (0,60,32), (32,0,60), (32,60,0), (60,0,32), (60,32,0),
  (2,10,60), (2,60,10), (10,2,60), (10,60,2), (60,2,10), (60,10,2)} := by
    ext ⟨x, y, z⟩
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      replace h: x * y * z + x * y + y * z + z * x + x + y + z + 1 = 2013 := by
        rw [h]
      rw [lemma_1] at h
      have d1: x + 1 ∈ Nat.divisors 2013 := by
        simp
        rw [← h]
        rw [show (x + 1) * (y + 1) * (z + 1) = (x + 1) * ((y + 1) * (z + 1)) by ring]
        simp
      have d2: y + 1 ∈ Nat.divisors 2013 := by
        simp
        rw [← h]
        rw [show (x + 1) * (y + 1) * (z + 1) = ((x + 1) * (z + 1)) * (y + 1) by ring]
        simp
      rw [show Nat.divisors 2013 = {1, 3, 11, 33, 61, 183, 671, 2013} by native_decide] at d1 d2
      simp at d1
      simp at d2
      rcases d1 with ex | ex | ex | ex | ex | ex | ex | ex
      all_goals simp [ex] at *
      all_goals rcases d2 with ey | ey | ey | ey | ey | ey | ey | ey
      <;> simp [ey] at *
      all_goals omega


    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals simp [h]


  -- then we can count the card
  rw [h_eq]
  clear h_eq
  simp [Set.encard_insert_of_not_mem]
  norm_num