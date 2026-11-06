import Mathlib

/- What is the maximum number of consecutive positive integers that can be added together before the sum exceeds 400?-/
theorem algebra_929 :
    IsGreatest {m | ∃ n : ℕ, n > 0 ∧ (∑ i ∈ Finset.range m, (n + i)) ≤ 400} 27 := by

  -- important lemma to simplify the sum
  have h (m n : ℕ): ∑ i ∈ Finset.range m, (n + i) = m * n + m * (m - 1) / 2 := by
    -- induction on m
    induction m with
    | zero => simp -- m = 0 is trivial
    | succ m hm =>
      -- simplify the sum by induction hypothetis
      simp [Finset.sum_range_succ, hm]
      -- simplify the expression
      ring_nf

      -- lemma to prove the expression
      have h1 : m * (m - 1) + m * 2 = m + m ^ 2 := by
        -- discuss m = 0 and m ≠ 0
        by_cases h : m = 0
        . -- when m = 0 its trivial
          rw [h]
          norm_num
        . -- when m ≠ 0
          replace h : m ≠ 0 := by omega
          -- prove it by calculation
          calc m * (m - 1) + m * 2 = m * (m - 1) + m + m := by omega
            _ = m * (m - 1 + 1) + m := by linarith
            _ = m * m + m := by rw [Nat.sub_one_add_one h] -- m - 1 + 1 = m
            _ = m + m ^ 2 := by ring

      -- prove the expression step by step
      calc m + m * n + n + m * (m - 1) / 2 = m * n + n + (m * (m - 1) / 2 + m) := by linarith -- rearrange the terms
        _ = m * n + n + ((m * (m - 1) + m * 2) / 2) := by rw [← Nat.add_mul_div_right _ _ (by linarith : 0 < 2)] -- factor out 2
        _ = m * n + n + ((m + m ^ 2) / 2) := by rw [h1] -- use h1 to rewrite the expression

  simp [IsGreatest, upperBounds]
  constructor -- split the goal into two
  . -- prove that 27 is valid
    use 1 -- n = 1
    constructor
    . linarith -- trivial
    . -- prove the sum is less than 400
      specialize h 27 1
      rw [h]
      norm_num

  . -- prove that 27 is an upper bound
    -- simplify the statement
    intro a x hx hsig
    replace hx : x ≥ 1 := by linarith
    -- substitute the sum expression
    specialize h a x
    rw [h] at hsig
    
    -- prove that a ≥ 28 is impossible
    contrapose! hsig
    replace hsig : 28 ≤ a := by linarith

    -- lemma as mid step in proof of inequality
    have ha : 28 * (28 - 1) ≤ a * (a - 1) := Nat.mul_le_mul (hsig) (Nat.sub_le_sub_right hsig 1)
    -- prove the inequality
    calc 400 < 406 := by linarith
      _ = 28 * 1 + 28 * (28 - 1) / 2 := by norm_num -- numerical calculation
      _ ≤ 28 * x + 28 * (28 - 1) / 2 := by linarith -- by 1 ≤ x
      _ ≤ a * x + 28 * (28 - 1) / 2 := Nat.add_le_add_right (Nat.mul_le_mul_right x hsig) _ -- by 28 ≤ a
      _ ≤ a * x + a * (a - 1) / 2 := Nat.add_le_add_left (Nat.div_le_div_right ha) (a * x) -- use lemma ha
