import Mathlib

/-
To derive the formula, we start with the base cost of 20 cents for the first ounce. For any additional weight beyond the first ounce, we need to account for the extra ounces. If we let $ x $ represent the total weight of the letter in ounces, the cost can be expressed as:
-/
noncomputable abbrev cost (w : ℝ) := if w ≤ 0 then 0 else 20 + 18 * (⌊w + 1 / 2⌋ - 1)

/-
To mail a letter in the United States, the cost is 20 cents for the first ounce and 18 cents for each additional ounce or any fraction of an ounce.
We need to find a formula that uses the greatest integer function to calculate the total cost of mailing a letter.
Additionally, we want to determine if it is possible for the mailing cost to be 1.08 or 1.28.
case 1. cost=1.08
-/
theorem number_theory_4924_1 : ¬ ∃ w, cost w = 108 := by
-- it is impossible to mail a letter for the first question,
-- so it is necessary to prove that there is no number that meets the requirements.
  contrapose; contrapose
  rw [not_not, not_not]
  rintro ⟨w, hw⟩
  rw [cost] at hw
  set x := ⌊w + 1 / 2⌋
  by_cases h : w ≤ 0
  -- w ≤ 0
  . simp [h] at hw
  -- w > 0
  . simp [h] at hw
    apply eq_sub_of_add_eq' at hw
    norm_num at hw
    -- 18 * (x - 1) = 88
    rw [mul_sub, mul_one] at hw
    -- 18 * x = 106
    apply_fun (· % 9) at hw
    rw [Int.sub_emod, Int.mul_emod] at hw
    norm_num at hw

/-
To mail a letter in the United States, the cost is 20 cents for the first ounce and 18 cents for each additional ounce or any fraction of an ounce.
We need to find a formula that uses the greatest integer function to calculate the total cost of mailing a letter.
Additionally, we want to determine if it is possible for the mailing cost to be 1.08 or 1.28.
case 2. cost=1.28
-/
theorem number_theory_4924_2 : ∃ w, cost w = 128 := by
-- it is possible to mail a letter for the second question,
-- so providing a solution that meets the requirements and substituting it in will suffice.
  use 7
  rw [cost]
  norm_num
