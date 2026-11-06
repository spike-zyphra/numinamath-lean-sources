import Mathlib

/-Alice, Bob, and Charlie roll a 4,5 , and 6 -sided die, respectively. What is the probability that a number comes up exactly twice out of the three rolls?
-/

open Finset


def die_A_outcomes : Finset ℕ := Icc 1 4
def die_B_outcomes : Finset ℕ := Icc 1 5
def die_C_outcomes : Finset ℕ := Icc 1 6

-- The sample space Ω is the set of all possible triplets (a, b, c) of outcomes.
def Ω : Finset (ℕ × ℕ × ℕ) :=
  Finset.product die_A_outcomes (Finset.product die_B_outcomes die_C_outcomes)

-- The event E is the set of outcomes where exactly two rolls are equal.
-- This can be partitioned into three disjoint cases.
def E₁ : Finset (ℕ × ℕ × ℕ) := -- A = B, A ≠ C
  Ω.filter (fun r => r.1 = r.2.1 ∧ r.1 ≠ r.2.2)

def E₂ : Finset (ℕ × ℕ × ℕ) := -- A = C, A ≠ B
  Ω.filter (fun r => r.1 = r.2.2 ∧ r.1 ≠ r.2.1)

def E₃ : Finset (ℕ × ℕ × ℕ) := -- B = C, B ≠ A
  Ω.filter (fun r => r.2.1 = r.2.2 ∧ r.2.1 ≠ r.1)

def E : Finset (ℕ × ℕ × ℕ) := E₁ ∪ E₂ ∪ E₃

-- The total number of outcomes is |A| * |B| * |C|.
lemma card_Ω : Ω.card = 120 := by
  simp [Ω, die_A_outcomes, die_B_outcomes, die_C_outcomes, card_product]
  decide

-- The number of outcomes for Case 1 (A=B, A≠C).
lemma card_E₁ : E₁.card = 20 := by

  let common_vals := die_A_outcomes ∩ die_B_outcomes

  have h_card : E₁.card = (common_vals).sum (fun x => (die_C_outcomes.filter (· ≠ x)).card) := by decide
  rw [h_card]
  have h_common_vals : common_vals = Icc 1 4 := by 
    simp [common_vals,die_A_outcomes, die_B_outcomes]
    decide
  rw [h_common_vals]
  -- For any x in {1,2,3,4}, the number of choices for C is 5.
  decide


-- The number of outcomes for Case 2 (A=C, A≠B).
lemma card_E₂ : E₂.card = 16 := by
  let common_vals := die_A_outcomes ∩ die_C_outcomes
  have h_card : E₂.card = (common_vals).sum (fun x => (die_B_outcomes.filter (· ≠ x)).card) := by decide
  rw [h_card]
  have h_common_vals : common_vals = Icc 1 4 := by     
    simp [common_vals,die_A_outcomes, die_B_outcomes]
    decide
  rw [h_common_vals]
  decide

-- The number of outcomes for Case 3 (B=C, B≠A).
lemma card_E₃ : E₃.card = 16 := by
  let common_vals := die_B_outcomes ∩ die_C_outcomes
  have h_card : E₃.card = (common_vals).sum (fun x => (die_A_outcomes.filter (· ≠ x)).card) := by decide
  rw [h_card]
  have h_common_vals : common_vals = Icc 1 5 := by 
    simp [common_vals,die_A_outcomes, die_B_outcomes]
    decide
  rw [h_common_vals]
  decide
  
theorem Combinatorics_610146 :
    (E.card : ℚ) / (Ω.card : ℚ) = 13 / 30 := by

  have h_disjoint12 : Disjoint E₁ E₂ := by decide
  have h_disjoint13 : Disjoint E₁ E₃ := by decide
  have h_disjoint23 : Disjoint E₂ E₃ := by decide

  have h_card_E : E.card = E₁.card + E₂.card + E₃.card := by
    rw [show E = (E₁ ∪ E₂) ∪ E₃ by rfl]
    apply card_union_of_disjoint 
    apply disjoint_union_left.mpr
    exact ⟨ h_disjoint13, h_disjoint23⟩ 

  rw [h_card_E, card_E₁, card_E₂, card_E₃, card_Ω]
  
  norm_num

