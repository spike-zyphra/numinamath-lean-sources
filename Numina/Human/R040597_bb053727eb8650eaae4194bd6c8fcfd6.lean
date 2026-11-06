import Mathlib

/-
What can you conclude if \( a \) and \( b \) are nonzero integers such that \( a \) divides \( b \) and \( b \) divides \( a \)?
-/
theorem number_theory_4703 {a b : ℤ} (_ : a ≠ 0) (hb : b ≠ 0) : a ∣ b ∧ b ∣ a → a = b ∨ a = -b := by
  intro h
  -- Extract the two divisibility conditions from the hypothesis
  rcases h with ⟨hab,hba⟩
  -- From a ∣ b, obtain an integer k such that b = a * k
  rcases hab with ⟨k,hk⟩
  -- From b ∣ a, obtain an integer m such that a = b * m
  rcases hba with ⟨m,hm⟩
  -- Substitute a = b * m into the equation b = a * k
  -- This gives: b = (b * m) * k = b * (m * k)
  rw [hm] at hk
  -- Now we have: b = b * (m * k)
  -- Since b ≠ 0, we can cancel b from both sides to get: 1 = m * k
  have hmk : m * k = 1 := by
    -- Rewrite the equation as b * (m * k) = b
    -- Since b ≠ 0, divide both sides by b to get m * k = 1
    apply Int.eq_of_mul_eq_mul_left hb
    linarith

  -- In ℤ, the only solutions to m * k = 1 are (m, k) = (1, 1) or (-1, -1)
  -- We perform case analysis.
  cases (Int.eq_one_or_neg_one_of_mul_eq_one' hmk) with
  | inl h' =>
    -- If m = 1 and k = 1, then a = b
    rw [h'.1] at hm
    left
    ring_nf at hm
    exact hm
  | inr h' =>
    -- If m = -1 and k = -1, then a = -b
    rw [h'.1] at hm
    right
    ring_nf at hm
    exact hm
