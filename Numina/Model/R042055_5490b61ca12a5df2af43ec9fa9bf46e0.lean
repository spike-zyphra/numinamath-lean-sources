import Mathlib

theorem number_theory_290265 (n : ℤ) (h₀ : ¬ 2 ∣ n) (h₁ : ¬ 3 ∣ n) (h₂ : ¬ 5 ∣ n) :
    480 ∣ n^8 - 1 := by
  have h3 : n % 2 = 1 :=  by 
    omega
  have h4 : n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  have h5 : n  % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega
  have h6 : n % 32 = 1 ∨ n % 32 = 3 ∨ n % 32 = 5 ∨ n % 32 = 7 ∨ 
            n % 32 = 9 ∨ n % 32 = 11 ∨ n % 32 = 13 ∨ n % 32 = 15 ∨ 
            n % 32 = 17 ∨ n % 32 = 19 ∨ n % 32 = 21 ∨ n % 32 = 23 ∨ 
            n % 32 = 25 ∨ n % 32 = 27 ∨ n % 32 = 29 ∨ n % 32 = 31 := by
    have h16 : n % 2 = 1 := h3
    omega
  have h7 : n ^ 8 % 32 = 1 := by
    rcases h6 with (h | h | h | h | h | h | h | h |  h |  h |  h |  h |  h |  h |  h |  h  ) <;> ( 
      have h8 : n^8 % 32 = 1 := by 
        norm_num [h, pow_two, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      exact h8 
    )
  have h8 : n ^ 8 % 3 = 1 := by
    rcases h4 with (h4 | h4)
    · simp [h4, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h4, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  have h9 : n ^ 8 % 5 = 1 := by
    rcases h5 with (h5 | h5 | h5 | h5)
    · simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    · simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
  omega