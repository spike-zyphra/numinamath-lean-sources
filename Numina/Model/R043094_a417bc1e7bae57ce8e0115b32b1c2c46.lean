import Mathlib


theorem number_theory_84138 : {(k, n) : ℕ × ℕ | 0 < k ∧ 0 < n ∧ k ^ 2 - 2016 = (3 ^ n : ℤ)} =
    {(45, 2)} := by
  ext ⟨k, n⟩
  simp [-one_div]
  constructor
  · -- Assume (k, n) satisfies the equation, prove (k, n) = (45, 2)
    rintro ⟨hk, hn, heq⟩
    have h1 : (k : ℤ) ^ 2 = (3 ^ n : ℤ) + 2016 := by
      have h2 : (k : ℤ) ^ 2 - 2016 = (3 ^ n : ℤ) := by
        exact_mod_cast heq
      linarith
    have h2 : k % 3 = 0 := by
      have eq1 : (k : ℤ) ^ 2 % 3 = 0 := by
        have eq2 : (k : ℤ) ^ 2 = (3 ^ n : ℤ) + 2016 := h1
        have eq3 : (k : ℤ) ^ 2 % 3 = ((3 ^ n : ℤ) + 2016) % 3 := by
          rw [eq2]
        have eq4 : ((3 ^ n : ℤ) + 2016) % 3 = 0 := by
          have eq5 : (3 ^ n : ℤ) % 3 = 0 := by
            have h6 : n > 0 := by linarith
            have h7 : (3 ^ n : ℤ) % 3 = 0 := by
              have h8 : ∀ (m : ℕ), m > 0 → (3 ^ m : ℤ) % 3 = 0 := by
                intro m hm
                induction m with
                | zero => linarith
                | succ m ih =>
                  cases m with
                  | zero => simp at hm ⊢
                  | succ m =>
                    simp [pow_two, pow_succ, Int.add_emod, Int.mul_emod] at ih ⊢
                    all_goals omega
              apply h8 n h6
            assumption
          have eq6 : (2016 : ℤ) % 3 = 0 := by norm_num
          omega
        omega
      have eq2 : (k : ℤ) % 3 = 0 := by
        have h8 : (k : ℤ) ^ 2 % 3 = 0 := eq1
        have h9 : (k : ℤ) % 3 = 0 ∨ (k : ℤ) % 3 = 1 ∨ (k : ℤ) % 3 = 2 := by
          omega
        rcases h9 with (h | h | h)
        · 
          omega
        · 
          have h10 : (k : ℤ) ^ 2 % 3 = 1 := by
            simp [pow_two, Int.mul_emod, h]
          omega
        · 
          have h10 : (k : ℤ) ^ 2 % 3 = 1 := by
            simp [pow_two, Int.mul_emod, h]
          omega
      omega
    have h3 : ∃ m : ℕ, k = 3 * m := by 
      refine' ⟨k / 3, by omega⟩
    rcases h3 with ⟨m, hm⟩
    have h4 : (3 * m : ℤ) ^ 2 = (3 ^ n : ℤ) + 2016 := by
      have h10 : (k : ℤ) ^ 2 = (3 ^ n : ℤ) + 2016 := h1
      rw [show (k : ℤ) = (3 * m : ℤ) by exact_mod_cast (by linarith)] at h10
      linarith
    have h8 : n ≤ 6 := by
      by_contra h
      push_neg at h
      have h9 : n ≥ 7 := by omega
      have h10 : (3 : ℤ) ^ n % 729 = 0 := by
        have h11 : n ≥ 6 := by omega
        have h12 : (3 : ℤ) ^ n % 729 = 0 := by
          have h13 : ∀ (m : ℕ), (3 : ℤ) ^ (m + 6) % 729 = 0 := by
            intro m
            induction m with
            | zero => norm_num
            | succ m ih =>
              simp [pow_add, pow_mul] at ih ⊢
              all_goals omega
          specialize h13 (n - 6)
          have h14 : n - 6 + 6 = n := by omega
          rw [h14] at h13
          omega
        assumption
      have h11 : (3 * m : ℤ) ^ 2 % 729 = 2016 % 729 := by
        have h12 : (3 * m : ℤ) ^ 2 = (3 : ℤ) ^ n + 2016 := h4
        have h13 : (3 * m : ℤ) ^ 2 % 729 = ((3 : ℤ) ^ n + 2016) % 729 := by
          rw [h12]
        have h14 : ((3 : ℤ) ^ n + 2016) % 729 = 2016 % 729 := by
          have h15 : (3 : ℤ) ^ n % 729 = 0 := h10
          simp [Int.add_emod, h15]
        omega
      have h16 : (3 * m : ℤ) ^ 2 % 81 = 72 := by
        omega
      have h17 : (m : ℤ) ^ 2 % 9 = 8 := by
        have h118 : (3 * m : ℤ) ^ 2 % 81 = 72 := h16
        have h119 : (9 * (m : ℤ) ^ 2 : ℤ) % 81 = 72 := by
          have h120 : (3 * m : ℤ) ^ 2 = 9 * (m : ℤ) ^ 2 := by
            ring
          rw [h120] at h118
          omega
        omega
      have h18 : (m : ℤ) ^ 2 % 9 = 0 ∨ (m : ℤ) ^ 2 % 9 = 1 ∨ (m : ℤ) ^ 2 % 9 = 3 ∨ (m : ℤ) ^ 2 % 9 = 4 ∨ (m : ℤ) ^ 2 % 9 = 7 := by
        have h19 : (m : ℤ) % 9 = 0 ∨ (m : ℤ) % 9 = 1 ∨ (m : ℤ) % 9 = 2 ∨ (m : ℤ) % 9 = 3 ∨ (m : ℤ) % 9 = 4 ∨ (m : ℤ) % 9 = 5 ∨ (m : ℤ) % 9 = 6 ∨ (m : ℤ) % 9 = 7 ∨ (m : ℤ) % 9 = 8 := by
          omega
        rcases h19 with (h | h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h, Int.sub_emod]
      omega
    interval_cases n <;> try { 
      norm_num at h4
      all_goals
      have h10 : m ≤ 32 := by
        nlinarith
      interval_cases m <;> omega
    }
  · -- Assume (k, n) = (45, 2), prove it satisfies the equation
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num