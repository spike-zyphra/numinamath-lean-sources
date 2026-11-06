import Mathlib

theorem number_theory_150150 (n : ℤ) :
    ¬ ∃ k, k^2 = 3 * n^2 - 1 := by
  rintro ⟨k, hk⟩
  have h1 : k ^ 2 % 3 = 0 ∨ k ^ 2 % 3 = 1 := by
    have h11 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
      omega
    rcases h11 with (h11 | h11 | h11)
    · -- case k % 3 = 0
      simp [pow_two, Int.add_emod, Int.mul_emod, h11, Int.sub_emod]
    · -- case k % 3 = 1
      simp [pow_two, Int.add_emod, Int.mul_emod, h11, Int.sub_emod]
    · -- case k % 3 = 2
      simp [pow_two, Int.add_emod, Int.mul_emod, h11, Int.sub_emod]
  -- Substitute k^2 from hk to get a contradiction in modulo 3 arithmetic
  have h2 : k ^ 2 % 3 = 2 := by 
    omega
  omega