import Mathlib

/-How many odd integers are there between $\frac{17}{4}$ and $\frac{35}{2}?$-/
theorem algebra_17143 : {x : ℤ | Odd x ∧ (17 : ℝ) / 4 < x ∧ x < (35 : ℝ) / 2}.ncard = 7 := by
  -- auxiliary lemma : the required set is {5, 7, 9, 11, 13, 15, 17}.
  have aux : {x : ℤ | Odd x ∧ (17 : ℝ) / 4 < x ∧ x < (35 : ℝ) / 2} = {5, 7, 9, 11, 13, 15, 17} := by
    ext x
    simp
    constructor <;> intro h
    · have : 4 < x := by
        have : (4 : ℝ) < x := by linarith
        norm_cast at this
      have : x < 18 := by
        have : x < (18 : ℝ) := by linarith
        norm_cast at this
      interval_cases x <;> tauto
    · rcases h with h | h | h | h | h | h | h <;> simp [h] <;>
       exact ⟨by exact Int.odd_iff.mpr rfl, by linarith, by linarith⟩
  -- Therefore, the number of odd integers between 17 / 4 and 35 / 2 is 7.
  simp [aux]
  have : ({5, 7, 9, 11, 13, 15, 17} : Finset ℤ).card = 7 := by simp
  convert this
  simp [Set.ncard_eq_toFinset_card']
