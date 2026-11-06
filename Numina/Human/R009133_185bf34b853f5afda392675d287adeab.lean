import Mathlib

/-How many positive factors of 96 are also multiples of 12?-/
theorem algebra_16322 : {x : ℕ | x ∣ 96 ∧ 12 ∣ x}.ncard = 4 := by
  -- an auxiliary lemma : the positive numbers are factors of 96 and also are multiples of 96 is 12, 24, 48, 96.
  have aux : {x : ℕ | x ∣ 96 ∧ 12 ∣ x} = {12, 24, 48, 96} := by
    ext x
    simp
    constructor <;> intro h
    · obtain ⟨⟨m, hm⟩, ⟨t, ht⟩⟩ := h
      simp [ht, mul_assoc] at hm
      have h1 : t * m = 8 := by linarith
      have h2 : t ∣ 8 := Dvd.intro m h1
      have : t ≤ 8 := Nat.le_of_dvd (by omega) h2
      interval_cases t <;>  tauto
    · rcases h with h | h | h | h <;> simp [h] <;> norm_num
  -- by the above lemma, the card of {12, 24, 48, 96} is 4. So there 
  -- are 4 factors of 96 that are multiples of 12.
  have : ({12, 24, 48, 96} : Finset ℕ).card = 4 := by native_decide
  rw [aux]
  convert this
  rw [Set.ncard_eq_toFinset_card _]
  simp
