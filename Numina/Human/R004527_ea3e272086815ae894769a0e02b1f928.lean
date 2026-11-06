import Mathlib

/- In the diagram, four different integers from 1 to 9 inclusive are placed in the four boxes in the top row.
The integers in the left two boxes are multiplied and the integers in the right two boxes are added and these results are then divided, as shown.
The final result is placed in the bottom box. Which of the following integers cannot appear in the bottom box?
![](https://cdn.mathpix.com/cropped/2024_04_20_46ead6524a8d61e21c51g-034.jpg?height=290&width=417&top_left_y=191&top_left_x=1296)
(A) 16
(B) 24
(C) 7
(D) 20
(E) 9

Part C: Each correct answer is worth 8. -/
theorem algebra_279681:
  (∀(a b c d:ℕ), a ∈ Finset.Icc 1 9 → b ∈ Finset.Icc 1 9 → c ∈ Finset.Icc 1 9 → d ∈ Finset.Icc 1 9 →
    a ≠ b → c ≠ d → (a*b:ℚ) / (c+d) ≠ 20) ∧
  (∃ a b c d, ({a,b,c,d}: Finset ℕ) ⊆ Finset.Icc 1 9 ∧
    ({a,b,c,d}:Finset ℕ).card = 4 ∧ (a*b:ℚ) / (c+d) = 16) ∧
  (∃ a b c d, ({a,b,c,d}: Finset ℕ) ⊆ Finset.Icc 1 9 ∧
    ({a,b,c,d}:Finset ℕ).card = 4 ∧ (a*b:ℚ) / (c+d) = 24) ∧
  (∃ a b c d, ({a,b,c,d}: Finset ℕ) ⊆ Finset.Icc 1 9 ∧
    ({a,b,c,d}:Finset ℕ).card = 4 ∧ (a*b:ℚ) / (c+d) = 7) ∧
  (∃ a b c d, ({a,b,c,d}: Finset ℕ) ⊆ Finset.Icc 1 9 ∧
    ({a,b,c,d}:Finset ℕ).card = 4 ∧ (a*b:ℚ) / (c+d) = 9)  := by

  constructor

  · -- prove ab/(c+d) cannot be 20.
    intro a b c d ha hb hc hd aneb cned
    simp only [Finset.mem_Icc] at ha hb hc hd

    -- since all these integers are distinct and from 1 to 9, so a × b is at most 72.
    have hab: a*b ≤ 72 := by
      by_cases aeq: a = 9
      · have hh1: a*b ≤ 9*b := Nat.mul_le_mul_right b ha.right
        have hh2: b ≤ 8 := by
          have: b < 9 := by
            apply lt_of_le_of_ne hb.right ?_
            simpa [← aeq] using aneb.symm
          exact Nat.le_of_lt_succ this
        replace hh2: 9*b ≤ 9*8 := Nat.mul_le_mul_left 9 hh2
        exact hh1.trans hh2
      · have ale: a ≤ 8 := by omega
        exact Nat.mul_le_mul ale hb.right

    -- and we find c+d is at least 3.
    have hcd: c+d ≥ 3 := by
      by_cases hc: c = 1
      · rw [hc] at cned
        replace hd: d ≥ 2 := by omega
        linarith only [hc, hd]
      · replace hc: c ≥ 2 := by omega
        linarith only [hc, hd.left]

    -- if c+d = 3, we find a x b = 60. but it turns out a x b cannot be 60.
    by_cases cdeq: c+d = 3
    · rintro heq
      replace heq: a*b = 60 := by
        qify at cdeq ⊢
        rw [cdeq] at heq
        linarith only [heq]
      -- a,b > 6, since the other is at most 9, and 6x9 = 54 < 60
      have agt: a > 6 := by
        by_contra!
        replace: a*b ≤ 6*9 := by
          exact Nat.mul_le_mul this hb.right
        norm_num [heq] at this
      have age: a ≥ 7 := by exact agt
      have bgt: b > 6 := by
        by_contra!
        replace: a*b ≤ 9*6 := by
          exact Nat.mul_le_mul ha.right this
        norm_num [heq] at this
      have bge: b ≥ 7 := by exact bgt
      -- check all possible a,b (7 ≤ a,b ≤ 9), we find they cannot reach 60.
      replace ha := ha.right
      replace hb := hb.right
      clear * - age bge ha hb heq
      absurd heq; clear heq
      revert b; revert a; decide
    · -- therefore c+d ≥ 4
      replace hcd: c+d ≥ 4 := by
        omega
      -- then if ab /(c+d) = 20, ab ≥ 80, contradiction.
      rintro heq
      have not_hab: a*b ≥ 80 := by
        qify at hcd ⊢
        have: (a*b:ℚ) = 20 * (c+d:ℚ) := by
          rw [← heq]
          have: (c+d:ℚ) ≠ 0 := by linarith only [hcd]
          rw [div_mul_cancel₀ _ this]
        rw [this]
        replace: 20*(4:ℚ) ≤ 20*(c+d) := mul_le_mul rfl hcd rfl rfl
        exact le_trans (by norm_num) this
      linarith only [hab, not_hab]
  · -- 16,24,7,9 are possible values.
    split_ands
    · -- 16 = (6x8)/(1+2)
      use 6,8,1,2
      native_decide
    · -- 24 = (8x9)/(1+2)
      use 8,9,1,2
      native_decide
    · -- 7 = (3x7)/(1+2)
      use 3,7,1,2
      native_decide
    · -- 9 = (3x9)/(1+2)
      use 3,9,1,2
      native_decide