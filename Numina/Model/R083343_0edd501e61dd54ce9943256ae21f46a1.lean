import Mathlib

theorem algebra_11583 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 5 ∣ n ∧ 7 ∣ n} = 2 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 5 ∣ n ∧ 7 ∣ n} = {35, 70} := by
    ext n
    simp [Finset.mem_Icc]
    constructor
    · -- Assume n is a two-digit integer which is divisible by 5 and 7
      intro hn
      rcases hn with ⟨⟨hn1, hn2⟩, h5, h7⟩
      interval_cases n <;> norm_num at *
      <;> omega
    · -- Assume n is in {35, 70}, prove it is in the original set
      rintro (rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  norm_num