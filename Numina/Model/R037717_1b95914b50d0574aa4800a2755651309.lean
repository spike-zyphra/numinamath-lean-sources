import Mathlib

theorem number_theory_261134 : IsLeast {x | 0 < x ∧ 2023 ∣ x ∧ ∃ n, x = n^2} (7 * 2023) := by
  constructor
  · -- Show that 7 * 2023 is in the set
    constructor
    · -- Show that 7 * 2023 > 0
      norm_num
    constructor
    · -- Show that 2023 divides 7 * 2023
      norm_num
    · -- Show existence of n
      use 119
      all_goals norm_num
  · -- Show there is no smaller element
    intro x h
    rcases h with ⟨hx_pos, hx_div, ⟨n, hn⟩⟩
    by_contra h
    push_neg at h
    have h1 : n ^ 2 < 7 * 2023 := by
      nlinarith [hn, h]
    have h2 : n ≤ 118 := by
      nlinarith [h1]
    -- Assume that n^2 divisible by 2023, need to find contradiction with n < 119.
    -- The proof goes via showing that n divisible by 119, which contradicts n < 119.
    -- Show that n divisible by 7 and 17
    -- First show n divisible by 7
    have h4 : n % 7 = 0 := by
      have h7 : n ^ 2 % 7 = 0 := by
        omega
      have h8 : n % 7 = 0 := by
        have h9 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
          omega
        rcases h9 with (h | h | h | h | h | h | h) <;> simp [h, pow_two, Nat.mul_mod] at h7 ⊢
        <;> try { tauto }
      assumption
    -- Show that n divisible by 17
    have h10 : n % 17 = 0 := by
      have h11 : n ^ 2 % 17 = 0 := by
        omega
      have h12 : n % 17 = 0 := by
        have h13 : n % 17 = 0 ∨ n % 17 = 1 ∨ n % 17 = 2 ∨ n % 17 = 3 ∨ n % 17 = 4 ∨ n % 17 = 5 ∨ n % 17 = 6 ∨ n % 17 = 7 ∨ n % 17 = 8 ∨ n % 17 = 9 ∨ n % 17 = 10 ∨ n % 17 = 11 ∨ n % 17 = 12 ∨ n % 17 = 13 ∨ n % 17 = 14 ∨ n % 17 = 15 ∨ n % 17 = 16 := by
          omega
        rcases h13 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_two, Nat.mul_mod] at h11 ⊢
        <;> try { tauto }
      assumption
    -- From n divisible by both 7 and 17, it is divisible by 119
    have h11 : n % 119 = 0 := by
      omega
    -- Since n < 119, n divisible by 119 means n = 0. This is a contradiction.
    have h12 : n = 0 := by
      omega
    -- Now this contradicts x > 0
    have h13 : x = 0 := by
      nlinarith [hn, h12]
    linarith [hx_pos, h13]