import Mathlib

/-What is the average of all positive integers that have three digits when written in base $5$, but two digits when written in base $8$? Write your answer in base $10$.-/
theorem number_theory_23490 : ∃ (A : Finset ℕ), A = {n : ℕ | (Nat.digits 5 n).length = 3 ∧ (Nat.digits 8 n).length = 2} ∧ ((∑ n ∈ A, n) : ℚ) / A.card = 44 := by
  have : {n : ℕ | (Nat.digits 5 n).length = 3 ∧ (Nat.digits 8 n).length = 2} = {n : ℕ | 25 ≤ n ∧ n < 64} := by
    --If an integer n has three digits in base 5 then 5 ^ 2 ≤ n < 5 ^ 3. If an integer n has two digits in base 8 then 8 ^ 1 ≤ n < 8 ^ 2. Then 25 ≤ n < 64.
    ext x; simp 
    by_cases hx : x = 0
    · rw [hx]; simp
  -- Compute the length of Nat.digits via Nat.digits_len
    rw [Nat.digits_len _ _ (by norm_num) hx, Nat.digits_len _ _ (by norm_num) hx, Nat.add_one, Nat.add_one]
    have aux₁ : 3 = (2:ℕ).succ := by norm_num
    have aux₂ : 2 = (1:ℕ).succ := by norm_num
    rw [aux₁]; nth_rw 2 [aux₂]; simp
  -- Compute Nat.log via Nat.log_eq_iff
    rw [Nat.log_eq_iff (by norm_num)]
    rw [Nat.log_eq_iff (by norm_num)]
    norm_num
    constructor
    · exact fun h => ⟨h.1.1, h.2.2⟩
    intro ⟨h₁, h₂⟩
    constructor
    · constructor; exact h₁; apply lt_of_lt_of_le h₂ (by norm_num)
    constructor; apply le_trans (by norm_num) h₁; exact h₂
-- Define $f$ to be the function $n+25$
  let f : ℕ ↪ ℕ := {
    toFun := fun n => n + 25
    inj' := by intro m n hmn; apply Nat.add_right_cancel hmn
  }
  have f_aux (n : ℕ) : f n = n + 25 := rfl
-- Fulfill the goal with $Finset.map f (Finset.range 39)$ and check it satisfies the desired properties
  use Finset.map f (Finset.range 39) 
  constructor
  · rw [this]; ext x; simp
    constructor
    · intro ⟨y, ⟨hy₁, hy₂⟩⟩
      rw [← hy₂, f_aux]
      constructor
      · apply le_add_self
      have := add_lt_add_right hy₁ 25
      norm_num at this
      exact this
    intro ⟨hx₁, hx₂⟩
    use x - 25
    have aux₁ : 64 = (63:ℕ).succ := rfl
    have aux₂ : 39 = (38:ℕ).succ := rfl
    rw [aux₁, Nat.lt_succ_iff] at hx₂
    rw [aux₂, Nat.lt_succ_iff]
    norm_num
    constructor; exact hx₂
    rw [f_aux, Nat.sub_add_cancel hx₁]
  simp
-- Compute the average of the numbers in $A$
  have : ∑ x ∈ Finset.range 39, f x = ∑ x ∈ Finset.range 39, (x + 25) := rfl
  qify at this; rw [this, Finset.sum_add_distrib, ← Nat.cast_sum, Finset.sum_range_id]
  norm_num
