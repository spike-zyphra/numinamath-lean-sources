import Mathlib

/-A rectangular prism has edge lengths that are all positive integers, and its volume is 2002.
If rectangular prisms with corresponding equal edge lengths are considered the same,
then the number of such rectangular prisms
A: There are 6 kinds

B: There are 12 kinds

C: There are 14 kinds

D: More than 16 kinds-/

theorem number_theory_628094:
    {(a, b, c) : ℕ × ℕ × ℕ | a ≤ b ∧ b ≤ c ∧ a * b * c = 2002}.encard = 14 := by

    -- 2002 = 2 * 7 * 11 * 13
    -- we directly compute the set
    have h_eq:
    {(a, b, c) : ℕ × ℕ × ℕ | a ≤ b ∧ b ≤ c ∧ a * b * c = 2002} =
    {(1, 1, 2002), (1, 2, 1001), (1, 7, 286), (1, 11, 182), (1, 13, 154), (1, 14, 143), (1, 22, 91), (1, 26, 77),
      (2, 7, 143), (2, 11, 91), (2, 13, 77), (7, 11, 26), (7, 13, 22), (11, 13, 14)} := by
        ext ⟨a, b, c⟩
        constructor
        -- forward direction
        .
          intro h
          simp at h
          rcases h with ⟨l1, l2, h⟩

          -- we first show that a, b are divisors of 2002
          have da: a ∣ 2002 := by
            rw [← h]
            rw [show a * b * c = a * (b * c) by ring]
            simp
          have db: b ∣ 2002 := by
            rw [← h]
            rw [show a * b * c = b * (a * c) by ring]
            simp

          -- then we show that a = 1, 2, 7, 11
          have sa: a = 1 ∨ a = 2 ∨ a = 7 ∨ a = 11 := by
            have l: a ^ 3 ≤ a * b * c := by
              calc
                a ^ 3 ≤ b * a ^ 2 := by nlinarith
                    _ = b * a * a := by ring
                    _ ≤ b * a * c := by apply Nat.mul_le_mul_left; linarith
                    _ = a * b * c := by ring
            rw [h] at l
            have la: a < 13 := by
              by_contra! o
              absurd l
              simp
              have o1: 169 ≤ a ^ 2 := by nlinarith
              nlinarith
            clear * - la da
            interval_cases a <;> omega

          -- then we check all cases of a
          rcases sa with s | s | s | s

          -- case a = 1
          .
            simp [s] at *
            have hb: b ∈ Nat.divisors 2002 := by
              simp
              exact db
            clear db
            have eq: Nat.divisors 2002 = {1, 2, 7, 11, 13, 14, 22, 26, 77, 91, 143, 154, 182, 286, 1001, 2002} := by
              native_decide
            rw [eq] at hb
            clear eq
            have lb: b < 45 := by
              by_contra! o
              have o1: 2025 ≤ b ^ 2 := by nlinarith
              nlinarith
            simp [lb] at hb
            clear l2 l1 da s
            rcases hb with t | t | t | t | t | t | t | t | t | t | t | t | t | t | t | t
            all_goals simp [t] at lb
            all_goals simp [t] at h
            all_goals simp [t]; omega

          -- case a = 2
          .
            simp [s] at *
            replace h: b * c = 1001 := by
              rw [show 2 * b * c = 2 * (b * c) by ring] at h
              omega
            have hb: b ∈ Nat.divisors 1001 := by
              simp
              rw [← h]
              simp
            clear db da s
            have eq: Nat.divisors 1001 = {1, 7, 11, 13, 77, 91, 143, 1001} := by
              native_decide
            rw [eq] at hb
            clear eq
            have lb: b < 32 := by
              by_contra! o
              have o1: 1024 ≤ b ^ 2 := by nlinarith
              nlinarith
            simp at hb
            rcases hb with t | t | t | t | t | t | t | t
            all_goals simp [t] at *
            all_goals omega

          -- case a = 7
          .
            simp [s] at *
            replace h: b * c = 286 := by
              rw [show 7 * b * c = 7 * (b * c) by ring] at h
              omega
            have hb: b ∈ Nat.divisors 286 := by
              simp
              rw [← h]
              simp
            clear db da s
            have eq: Nat.divisors 286 = {1, 2, 11, 13, 22, 26, 143, 286} := by
              native_decide
            rw [eq] at hb
            clear eq
            have lb: b < 17 := by
              by_contra! o
              have o1: 289 ≤ b ^ 2 := by nlinarith
              nlinarith
            simp at hb
            rcases hb with t | t | t | t | t | t | t | t
            all_goals simp [t] at *
            all_goals omega

          -- case a = 11
          .
            simp [s] at *
            replace h: b * c = 182 := by
              rw [show 11 * b * c = 11 * (b * c) by ring] at h
              omega
            have hb: b ∈ Nat.divisors 182 := by
              simp
              rw [← h]
              simp
            clear db da s
            have eq: Nat.divisors 182 = {1, 2, 7, 13, 14, 26, 91, 182} := by
              native_decide
            rw [eq] at hb
            clear eq
            have lb: b < 14 := by
              by_contra! o
              have o1: 196 ≤ b ^ 2 := by nlinarith
              nlinarith
            simp at hb
            rcases hb with t | t | t | t | t | t | t | t
            all_goals simp [t] at *
            all_goals omega


        -- backward direction
        .
          intro h
          simp
          simp at h
          rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
          all_goals simp [h]



    -- then we can compute the size of the set
    rw [h_eq]
    simp [Set.encard_insert_of_not_mem]
    norm_num