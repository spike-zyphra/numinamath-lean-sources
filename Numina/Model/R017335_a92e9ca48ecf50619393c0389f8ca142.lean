import Mathlib

theorem number_theory_231886 :
    Set.ncard {n : ℕ | n > 0 ∧ 24 ∣ n ∧ (n = 2^2 * 3^2 * 5^2 * 7^3 ∨ n = 2^2 * 3^2 * 5^3 * 7^2 ∨ n = 2^2 * 3^3 * 5^2 * 7^2 ∨ n = 2^3 * 3^2 * 5^2 * 7^2)} = 1 := by
  have h1 : {n : ℕ | n > 0 ∧ 24 ∣ n ∧ (n = 2^2 * 3^2 * 5^2 * 7^3 ∨ n = 2^2 * 3^2 * 5^3 * 7^2 ∨ n = 2^2 * 3^3 * 5^2 * 7^2 ∨ n = 2^3 * 3^2 * 5^2 * 7^2)} = {2^3 * 3^2 * 5^2 * 7^2} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume n is in the left side, prove it is equal to the right side.
      rintro ⟨hn_pos, hn_div_24, heq⟩
      rcases heq with (h | h | h | h)
      · -- Case 1
        norm_num [h] at hn_div_24
      · -- Case 2
        norm_num [h] at hn_div_24
      · -- Case 3
        norm_num [h] at hn_div_24
      · -- Case 4
        norm_num at h ⊢
        omega
    · -- Assume n is equal to the right side, prove it is in the left side.
      intro h
      rw [h]
      constructor
      · -- Show 2^3 * 3^2 * 5^2 * 7^2 > 0
        norm_num
      constructor
      · -- Show 24 divides 2^3 * 3^2 * 5^2 * 7^2
        norm_num
      · -- Show disjunction
        simp
  rw [h1]
  simp