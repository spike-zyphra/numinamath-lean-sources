import Mathlib

--Proof: Impossible to make all cells 2012 in a 5x5 grid: Initial weighted sum is 0, each operation adds a multiple of 22, so final sum must be divisible by 22. But 138*2012 ≡ 16 (mod 22) ≠ 0, hence the target state is impossible.

-- Increment per operation (from reference solution)
def Increment : ℕ := 22

--Verify that for the given 5x5 grid, each operation increases the weighted sum by exactly 22

-- Define weight matrix for the 5x5 grid
def weight (i j : ℕ) : ℕ :=
  if i = 0 then
    if j = 0 then 8 else if j = 1 then 7 else if j = 2 then 5 else if j = 3 then 7 else 8
  else if i = 1 then
    if j = 0 then 7 else if j = 1 then 2 else if j = 2 then 3 else if j = 3 then 2 else 7
  else if i = 2 then
    if j = 0 then 5 else if j = 1 then 3 else if j = 2 then 10 else if j = 3 then 3 else 5
  else if i = 3 then
    if j = 0 then 7 else if j = 1 then 2 else if j = 2 then 3 else if j = 3 then 2 else 7
  else  -- i = 4
    if j = 0 then 8 else if j = 1 then 7 else if j = 2 then 5 else if j = 3 then 7 else 8


-- Compute increment when operating cell (i,j) (self + adjacent weights)
def increment (i j : ℕ) : ℕ :=
  weight i j  -- self weight
  + (if i > 0 then weight (i-1) j else 0)  -- top neighbor
  + (if i < 4 then weight (i+1) j else 0)  -- bottom neighbor
  + (if j > 0 then weight i (j-1) else 0)  -- left neighbor
  + (if j < 4 then weight i (j+1) else 0)  -- right neighbor

-- Prove increment is 22 for all positions
theorem all_increments_eq_22 : ∀ i j, 0 ≤ i ∧ i ≤ 4 ∧ 0 ≤ j ∧ j ≤ 4 → increment i j = Increment := by
  -- Iterate over all 25 cells
  intro i j h
  -- Compute by position type
  match i, j with
  -- Corner positions
  | 0, 0 => rfl  -- 8+7+7=22
  | 0, 4 => rfl  -- 8+7+7=22
  | 4, 0 => rfl  -- 8+7+7=22
  | 4, 4 => rfl  -- 8+7+7=22

  -- Edge non-corner positions
  | 0, 1 => rfl  -- 7+8+5+2=22
  | 0, 2 => rfl  -- 5+7+7+3=22
  | 0, 3 => rfl  -- 7+8+5+2=22
  | 1, 0 => rfl  -- 7+8+5+2=22
  | 1, 4 => rfl  -- 7+8+5+2=22
  | 2, 0 => rfl  -- 5+7+7+3=22
  | 2, 4 => rfl  -- 5+7+7+3=22
  | 3, 0 => rfl  -- 7+8+5+2=22
  | 3, 4 => rfl  -- 7+8+5+2=22
  | 4, 1 => rfl  -- 7+8+5+2=22
  | 4, 2 => rfl  -- 5+7+7+3=22
  | 4, 3 => rfl  -- 7+8+5+2=22

  -- Inner positions
  | 1, 1 => rfl  -- 2+7+3+7+3=22
  | 1, 2 => rfl  -- 3+5+10+2+2=22
  | 1, 3 => rfl  -- 2+7+3+7+3=22
  | 2, 1 => rfl  -- 3+2+2+5+10=22
  | 2, 2 => rfl  -- 10+3+3+3+3=22
  | 2, 3 => rfl  -- 3+2+2+5+10=22
  | 3, 1 => rfl  -- 2+7+3+7+3=22
  | 3, 2 => rfl  -- 3+5+10+2+2=22
  | 3, 3 => rfl  -- 2+7+3+7+3=22


-- Compute total weight sum (should be 138)
def total_weight : ℕ :=
  let rows := [0,1,2,3,4]
  (rows.flatMap fun i => rows.map fun j => weight i j).sum


-- Verify total weight is 138
lemma total_weight_eq_138 : total_weight = 138 := by
  unfold total_weight
  rfl

-- Target value for each cell
def target : ℕ := 2012

-- Final weighted sum = total_weight × target
def final_sum := total_weight * target

-- Proof that final_sum is not divisible by 22
theorem not_divisible : ¬ Increment ∣ final_sum := by
  unfold Increment final_sum target
  rw [total_weight_eq_138]

  -- Definition: increment ∣ final_sum iff final_sum % increment = 0
  rw [Nat.dvd_iff_mod_eq_zero]
  -- Compute 138 mod 22
  have h138 : 138 % 22 = 6 := by rfl  -- 22*6=132, 138-132=6

  -- Compute 2012 mod 22
  have h2012 : 2012 % 22 = 10 := by norm_num

  -- Compute (138 * 2012) mod 22 = (6 * 10) mod 22
  rw [Nat.mul_mod, h138, h2012]

  -- Compute 60 mod 22 = 16
  have h60 : 60 % 22 = 16 := by rfl

  -- Conclusion: 16 ≠ 0
  rw [h60]
  norm_num
