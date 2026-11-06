import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_140196 (x : ℝ) (hx : x ≠ 4) :
    {y | ∃ x : ℝ, x ≠ 4 ∧ y = max (max 5 (max (min x 4) (min 4 x))) (min 5 (min (max x 4) (max 4 x)))}.ncard = 1 := by
  have h1 : {y | ∃ x : ℝ, x ≠ 4 ∧ y = max (max 5 (max (min x 4) (min 4 x))) (min 5 (min (max x 4) (max 4 x)))} = {5} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume there exists an x ≠ 4 such that y equals the expression
      rintro ⟨x, hx, heq⟩
      have h3 : min (4 : ℝ) x = min x (4 : ℝ) := by 
        cases min_cases x (4 : ℝ) with
        | inl h =>
          cases min_cases (4 : ℝ) x with
          | inl h' =>
            linarith
          | inr h' =>
            linarith
        | inr h =>
          cases min_cases (4 : ℝ) x with
          | inl h' =>
            linarith
          | inr h' =>
            linarith
      have h4 : max (4 : ℝ) x = max x (4 : ℝ) := by 
        cases max_cases x (4 : ℝ) with
        | inl h =>
          cases max_cases (4 : ℝ) x with
          | inl h' =>
            linarith
          | inr h' =>
            linarith
        | inr h =>
          cases max_cases (4 : ℝ) x with
          | inl h' =>
            linarith
          | inr h' =>
            linarith
      have eq1 : max (min x 4) (min (4 : ℝ) x) = min x (4 : ℝ) := by 
        rw [h3]
        simp
      have eq2 : max 5 (max (min x 4) (min (4 : ℝ) x)) = 5 := by
        rw [eq1]
        have h : min x (4 : ℝ) ≤ (4 : ℝ) := by 
          cases min_cases x (4 : ℝ) with
          | inl h1 =>
            linarith
          | inr h2 =>
            linarith
        have h' : min x (4 : ℝ) ≤ (5 : ℝ) := by 
          linarith [show min x (4 : ℝ) ≤ (4 : ℝ) by cases min_cases x (4 : ℝ) <;> linarith]
        cases max_cases 5 (min x (4 : ℝ)) with
        | inl h1 =>
          linarith
        | inr h2 =>
          linarith
      have eq3 : min (max x (4 : ℝ) ) (max (4 : ℝ) x) = max x (4 : ℝ) := by
        rw [h4]
        all_goals simp
      have eq4 : min 5 (min (max x (4 : ℝ) ) (max (4 : ℝ) x)) = min 5 (max x (4 : ℝ)) := by
        rw [eq3]
      have eq5 : max (max 5 (max (min x 4) (min (4 : ℝ) x))) (min 5 (min (max x (4 : ℝ) ) (max (4 : ℝ) x))) = 5 := by
        rw [eq2, eq4]
        cases max_cases 5 (min 5 (max x (4 : ℝ))) with
        | inl h1 =>
          linarith
        | inr h2 =>
          have h3 : min 5 (max x (4 : ℝ)) ≤ (5 : ℝ) := by 
            cases min_cases 5 (max x (4 : ℝ)) with
            | inl h1 =>
              linarith
            | inr h2 =>
              linarith
          nlinarith
      have eq6 : max (max 5 (max (min x 4) (min (4 : ℝ) x))) (min 5 (min (max x (4 : ℝ) ) (max (4 : ℝ) x))) = 5 := eq5
      rw [eq6] at heq
      linarith
    · -- Assume y = 5, prove there exists x such that expression=5
      intro heq
      rw [heq]
      refine' ⟨0, by norm_num, by norm_num⟩
  rw [h1]
  simp