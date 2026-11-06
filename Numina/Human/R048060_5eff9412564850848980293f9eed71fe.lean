import Mathlib

set_option maxHeartbeats 600000

/-Spinner I is divided into four equal sections labeled 2, 3, 4 and 5. Spinner II is divided into five equal sections labeled 1, 3, 5, 7 and 9. If each spinner is spun and the resulting numbers are multiplied, what is the probability that the product is a two-digit even number? Express your answer as a common fraction.-/
theorem algebra_19901 : 
  let I : Fin 4 → ℕ := fun i => Fin.casesOn i (fun val _ => match val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | _ => 0 );
  let II : Fin 5 → ℕ := fun i => Fin.casesOn i (fun val _ => match val with
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 9
  | _ => 0 );
  let products := {x | ∃ i j, x = I i * II j };
  {x | ∃ i j, x = I i * II j ∧ Even x ∧ x ∈ Finset.Icc 10 99}.ncard / (4 * 5) = 7 / 20 := by
-- Define a function I mapping elements of Fin 4 to natural numbers.
  intro I
-- Define a function II mapping elements of Fin 5 to natural numbers.
  intro II
-- Define the set 'products' as the set of all products of I i and II j.
  intro products
  -- Prove that for all i in Fin 4, I i is one of 2, 3, 4, or 5.
  have hI (i : Fin 4) : I i = 2 ∨ I i = 3 ∨ I i = 4 ∨ I i = 5 := by
    fin_cases i; all_goals simp [I]

  -- Prove that for all i in Fin 5, II i is one of 1, 3, 5, 7, or 9.
  have hII (i : Fin 5) : II i = 1 ∨ II i = 3 ∨ II i = 5 ∨ II i = 7 ∨ II i = 9 := by
    fin_cases i; all_goals simp [II]

  -- Explicitly list all possible products of I i and II j.
  have all_products : products = { 2, 6, 10, 14, 18, 3, 9, 15, 21, 27, 4, 12, 20, 28, 36, 5, 15, 25, 35, 45} := by
    simp [products]; ext x
    refine ⟨?_, fun h₂ => ?_⟩
    · intro ⟨i, j, h⟩
      rw [h]
      have hi := hI i
      have hj := hII j
      rcases hi with hi | hi | hi | hi <;> rcases hj with hj | hj | hj | hj | hj
      all_goals rw [hi, hj]; decide
    simp at *
    rcases h₂ with u | u | u | u | u | u | u | u | u | u | u | u | u | u | u | u | u | u | u
    · rw [u]; use 0, 0; tauto
    · rw [u]; use 0, 1; tauto
    · rw [u]; use 0, 2; tauto
    · rw [u]; use 0, 3; tauto
    · rw [u]; use 0, 4; tauto
    · rw [u]; use 1, 0; tauto
    · rw [u]; use 1, 1; tauto
    · rw [u]; use 1, 3; tauto
    · rw [u]; use 1, 4; tauto
    · rw [u]; use 2, 0; tauto
    · rw [u]; use 2, 1; tauto
    · rw [u]; use 2, 2; tauto
    · rw [u]; use 2, 3; tauto
    · rw [u]; use 2, 4; tauto
    · rw [u]; use 3, 0; tauto
    · rw [u]; use 3, 1; tauto
    · rw [u]; use 3, 2; tauto
    · rw [u]; use 3, 3; tauto
    · rw [u]; use 3, 4; tauto
  -- List the even numbers between 10 and 99 that are in 'products'.
  have h_cases : {x | ∃ i j, x = I i * II j ∧ Even x ∧ x ∈ Finset.Icc 10 99} =
    {10, 14, 18, 12, 20, 28, 36} := by
        ext x; constructor
        · rintro ⟨i, j, hx⟩
          rcases hI i with hi | hi | hi | hi <;> rcases hII j with hj | hj | hj | hj | hj
          any_goals simp [hx, hi, hj] at *
          all_goals contradiction
        · intro hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        -- Case: 10 = 2 * 5
          use 0, 2; constructor
          have h1 : I 0 = 2 := by simp [I]
          have h2 : II 2 = 5 := by simp [II]
          rw [h1, h2]
          norm_num
          exact (Nat.even_iff).mpr (by norm_num)
        -- Case: 14 = 2 * 7
          use 0, 3; constructor
          have h1 : I 0 = 2 := by simp [I]
          have h2 : II 3 = 7 := by simp [II]
          rw [h1, h2]
          norm_num; use 7
        -- Case: 18 = 2 * 9 
          use 0, 4; constructor
          have h1 : I 0 = 2 := by simp [I]
          have h2 : II 4 = 9 := by simp [II]
          rw [h1, h2]
          norm_num; use 9
        -- Case: 12 = 4 * 3
          use 2, 1; constructor
          have h1 : I 2 = 4 := by simp [I]
          have h2 : II 1 = 3 := by simp [II]
          rw [h1, h2]
          norm_num; use 6
        -- Case: 20 = 4 * 5  
          use 2, 2; constructor
          have h1 : I 2 = 4 := by simp [I]
          have h2 : II 2 = 5 := by simp [II]
          rw [h1, h2]
          norm_num; use 10
        -- Case: 28 = 4 * 7
          use 2, 3; constructor
          have h1 : I 2 = 4 := by simp [I]
          have h2 : II 3 = 7 := by simp [II]
          rw [h1, h2]
          norm_num; use 14
        -- Case: 36 = 4 * 9 
          use 2, 4; constructor
          have h1 : I 2 = 4 := by simp [I]
          have h2 : II 4 = 9 := by simp [II]
          rw [h1, h2]
          norm_num; use 18

  -- Calculate the total number of possible products (4 * 5 = 20).
  have h_total : 4 * 5 = 20 := by norm_num

  -- Calculate the cardinality of the set of even numbers between 10 and 99 in 'products'.
  have h_card : {x | ∃ i j, x = I i * II j ∧ Even x ∧ x ∈ Finset.Icc 10 99}.ncard = 7 := by
    rw [h_cases]; norm_num

  -- Calculate the final proportion.
  calc {x | ∃ i j, x = I i * II j ∧ Even x ∧ x ∈ Finset.Icc 10 99}.ncard / (4 * 5)
      = 7 / 20 := by rw [h_card, h_total]