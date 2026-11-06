import Mathlib

-- Let A and B be two different two-digit numbers that have the same last digit. It is known that the quotient of A divided by 9 equals the remainder of B divided by 9, and the quotient of B divided by 9 equals the remainder of A divided by 9. Find all such pairs of numbers (A, B).
theorem number_theorem_210996
  (A B a b c : ℕ)
  (ha : 0 < a ∧ a ≤ 9)
  (hb : 0 < b ∧ b ≤ 9)
  (hc : c ≤ 9)
  (hA : A = 10 * a + c)
  (hB : B = 10 * b + c)
  (hAB : A > B)
  (hAB1 : A / 9 = B % 9)
  (hAB2 : B / 9 = A % 9) :
  A = 75 ∧ B = 35 ∨ A = 65 ∧ B = 25 ∨ A = 55 ∧ B = 15 := by

  -- Step 1: Express A / 9 and A % 9 in terms of a and c
  have hAeq1 : A / 9 = a + (a + c) / 9 := by
    rw [hA]
    omega
  have hAeq2 : A % 9 = (a + c) % 9 := by
    rw [hA]
    omega

  -- Step 2: Express B / 9 and B % 9 in terms of b and c
  have hBeq1 : B / 9 = b + (b + c) / 9 := by
    rw [hB]
    omega
  have hBeq2 : B % 9 = (b + c) % 9 := by
    rw [hB]
    omega

  -- Step 3: Substitute these into the original constraints
  rw [hAeq1, hBeq2] at hAB1
  rw [hAeq2, hBeq1] at hAB2

  -- Step 4: Since A > B, we must have a > b (the tens digit is larger)
  have hab : a > b := by nlinarith

  -- Step 5: Helper facts about division and modulus for numbers < 18
  have h1 : ∀ n, n ≥ 9 ∧ n ≤ 17 → n / 9 = 1 ∧ n % 9 = n - 9 := by
    intro n hn
    omega
  have h2 : ∀ n, n < 9 → n / 9 = 0 ∧ n % 9 = n := by
    intro n hn
    omega

  -- Step 6: Split into cases based on whether a+c is at least 9
  by_cases hac : a + c ≥ 9

  -- CASE 1: a + c ≥ 9
  · by_cases hac' : a + c > 17
    -- Subcase 1.1: a + c ≥ 18
    · have : a + c ≥ 18 := by exact hac'
      -- Since a ≤ 9, c ≤ 9, this only happens if both are 9
      have : a ≥ 9 := by linarith
      have haeq : a = 9 := by linarith
      have : c ≥ 9 := by linarith
      have hceq : c = 9 := by linarith
      rw [haeq, hceq] at hAB1
      simp at hAB1
      -- Contradiction: b % 9 < 9, but would require b % 9 = 9
      have : b % 9 < 9 := Nat.mod_lt b (by linarith)
      rw [← hAB1] at this
      linarith

    -- Subcase 1.2: 9 ≤ a + c ≤ 17
    · simp at hac'
      by_cases hbc : b + c ≥ 9
      -- Subsubcase 1.2.1: b + c > 17
      · by_cases hbc' : b + c > 17
        · have : b + c ≥ 18 := by exact hbc'
          have : b ≥ 9 := by linarith
          have hbeq : b = 9 := by linarith
          have : c ≥ 9 := by linarith
          have hceq : c = 9 := by linarith
          rw [hbeq, hceq] at hAB2
          simp at hAB2
          -- Contradiction as above
          have : a % 9 < 9 := Nat.mod_lt a (by linarith)
          rw [← hAB2] at this
          linarith
        -- Subsubcase 1.2.2: 9 ≤ b + c ≤ 17
        · simp at hbc'
          rcases (h1 (a+c) ⟨hac, hac'⟩) with ⟨haceq1, haceq2⟩
          rcases (h1 (b+c) ⟨hbc, hbc'⟩) with ⟨hbceq1, hbceq2⟩
          rw [haceq1, hbceq2] at hAB1
          rw [haceq2, hbceq1] at hAB2
          -- Only possible if c = 10, but c ≤ 9, contradiction
          have : c = 10 := by omega
          linarith
      -- Subsubcase 1.2.3: b + c < 9
      · simp at hbc
        rcases (h1 (a+c) ⟨hac, hac'⟩) with ⟨haceq1, haceq2⟩
        rcases (h2 (b+c) hbc) with ⟨hbceq1, hbceq2⟩
        rw [haceq1, hbceq2] at hAB1
        rw [haceq2, hbceq1] at hAB2
        -- Now, solve for c and b using the constraints
        have hceq : c = 5 := by omega
        have : b < 4 := by linarith
        -- Try all possible b = 1, 2, 3
        by_cases hb1 : b = 1
        · have : a = 5 := by omega
          simp [this, hceq] at hA
          simp [hb1, hceq] at hB
          right
          right
          exact ⟨hA, hB⟩
        · by_cases hb2 : b = 2
          · have : a = 6 := by omega
            simp [this, hceq] at hA
            simp [hb2, hceq] at hB
            right
            left
            exact ⟨hA, hB⟩
          · by_cases hb3 : b = 3
            · have : a = 7 := by omega
              simp [this, hceq] at hA
              simp [hb3, hceq] at hB
              left
              exact ⟨hA, hB⟩
            · have : b > 4 := by omega
              linarith

  -- CASE 2: a + c < 9
  · simp at hac
    have hbc : b + c < 9 := by linarith
    rcases (h2 (a+c) hac) with ⟨haceq1, haceq2⟩
    rcases (h2 (b+c) hbc) with ⟨hbceq1, hbceq2⟩
    rw [haceq1, hbceq2] at hAB1
    rw [haceq2, hbceq1] at hAB2
    -- This case forces c = 0 and a = b, which contradicts a > b
    have : c = 0 := by omega
    have : a = b := by omega
    linarith
