import Mathlib

/-!
There exist unique nonnegative integers A, B (0 ≤ A, B ≤ 9)
such that (1001 * A + 110 * B)^2 = 57108249.
Find 10 * A + B.
-/

theorem find_AB : ∃ A B : ℕ, A ≤ 9 ∧ B ≤ 9 ∧
  (1001 * A + 110 * B)^2 = 57108249 ∧ 10 * A + B = 75 := by

  -- Let A = 7 and B = 5, candidate values for which the equation may hold
  let A := 7
  let B := 5

  -- Prove that A is a valid digit (0 ≤ A ≤ 9)
  have hA : A ≤ 9 := by norm_num

  -- Prove that B is a valid digit (0 ≤ B ≤ 9)
  have hB : B ≤ 9 := by norm_num

  -- Verify the square condition: (1001 * A + 110 * B)^2 = 57108249
  have h_sq : (1001 * A + 110 * B)^2 = 57108249 := by norm_num

  -- Verify that 10 * A + B gives the final answer: 10 * 7 + 5 = 75
  have h_ans : 10 * A + B = 75 := by norm_num

  -- Return the tuple ⟨A, B, constraints⟩ showing the existence of such A, B
  exact ⟨A, B, hA, hB, h_sq, h_ans⟩