import Mathlib

theorem number_theory_283883 (a : ℤ) (ha : ¬ 4 ∣ a ∧ a % 10 = 4) :
    480 ∣ a * (a^2 - 1) * (a^2 - 4) := by 
  rcases ha with ⟨ha1, ha2⟩ 
  have h1 : a % 2 = 0 := by 
    omega 
  -- Prove divisibility by 3
  have h5' : a * (a ^ 2 - 1) * (a ^ 2 - 4) % 3 = 0 := by
    have h2 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
      omega
    rcases h2 with (h | h | h)
    · simp [h, Int.mul_emod, Int.sub_emod, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h, Int.mul_emod, Int.sub_emod, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h, Int.mul_emod, Int.sub_emod, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
  -- Prove divisibility by 5
  have h5'' : a * (a ^ 2 - 1) * (a ^ 2 - 4) % 5 = 0 := by
    have h3 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
      omega
    rcases h3 with (h | h | h | h | h)
    · simp [h, Int.mul_emod, Int.sub_emod, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h, Int.mul_emod, Int.sub_emod, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h, Int.mul_emod, Int.sub_emod, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h, Int.mul_emod, Int.sub_emod, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h, Int.mul_emod, Int.sub_emod, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
  -- Prove divisibility by 32
  have h5 : a * (a ^ 2 - 1) * (a ^ 2 - 4) % 32 = 0 := by 
    have h2 : a % 2 = 0 := h1 
    -- deriving more constraints
    have h55 : a % 4 = 2 := by
      omega 
    -- Now dividing into cases of a % 8 
    have h6 : a % 8 = 2 ∨ a % 8 = 6 := by
      omega
    rcases h6 with (h6 | h6)
    · -- a % 8 = 2 
      have h7 : a % 32 = 2 ∨ a % 32 = 10 ∨ a % 32 = 18 ∨ a % 32 = 26 := by
        omega 
      rcases h7 with (h7 | h7 | h7 | h7) <;> simp [h7, Int.mul_emod, Int.sub_emod, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] 
    · -- a % 8 = 6 
      have h8 : a % 32 = 6 ∨ a % 32 = 14 ∨ a % 32 = 22 ∨ a % 32 = 30 := by 
        omega 
      rcases h8 with (h8 | h8 | h8 | h8) <;> simp [h8, Int.mul_emod, Int.sub_emod, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod]
  omega