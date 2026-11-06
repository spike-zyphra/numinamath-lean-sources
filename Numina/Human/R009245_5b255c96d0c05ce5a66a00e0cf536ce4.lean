import Mathlib

/- How many integers between 1 and 200 are multiples of both 3 and 5 but not of either 4 or 7? -/
theorem algebra_12983 :
    Set.ncard {x : ℕ | 1 ≤ x ∧ x ≤ 200 ∧ 3 ∣ x ∧ 5 ∣ x ∧ ¬(4 ∣ x) ∧ ¬(7 ∣ x)} = 9 := by
  -- Write this set as a Finset
  have K : {x : ℕ | 1 ≤ x ∧ x ≤ 200 ∧ 3 ∣ x ∧ 5 ∣ x ∧ ¬(4 ∣ x) ∧ ¬(7 ∣ x)} = ((Finset.Icc 1 200).filter (λ x => 3 ∣ x ∧ 5 ∣ x)).filter (λ x => ¬(4 ∣ x) ∧ ¬(7 ∣ x)) := by
    rw [Finset.filter_filter]
    ext x
    simp
    tauto

  -- First, we pick out the multiples of 3 and 5
  -- They are multiples of 15
  -- Which are 15, 30, 45, 60, 75, 90, 105, 120, 135, 150, 165, 180, 195
  have H1 : (Finset.Icc 1 200).filter (λ x => 3 ∣ x ∧ 5 ∣ x) = {15, 30, 45, 60, 75, 90, 105, 120, 135, 150, 165, 180, 195} := by
    rfl

  -- Then we remove the multiples of 4 and 7
  -- And we are left with 15, 30, 45, 75, 90, 135, 150, 165, 195
  have H2 : ((Finset.Icc 1 200).filter (λ x => 3 ∣ x ∧ 5 ∣ x)).filter (λ x => ¬(4 ∣ x) ∧ ¬(7 ∣ x)) = {15, 30, 45, 75, 90, 135, 150, 165, 195} := by
    rw [H1]
    rfl

  -- Now we apply the previous results
  rw [K, H2, Set.ncard_coe_Finset]
  rfl
