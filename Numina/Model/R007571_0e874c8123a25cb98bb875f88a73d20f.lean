import Mathlib

theorem algebra_14367 :
    {n : ℤ | 0 < n ∧ 16 - (4 * n) > 10}.ncard = 1 := by
  have h1 : {n : ℤ | 0 < n ∧ 16 - (4 * n) > 10} = {1} := by
    ext n
    simp
    constructor
    · intro h
      rcases h with ⟨h1, h2⟩
      omega
    · intro h
      rw [h]
      constructor
      · norm_num
      · norm_num
  rw [h1]
  simp