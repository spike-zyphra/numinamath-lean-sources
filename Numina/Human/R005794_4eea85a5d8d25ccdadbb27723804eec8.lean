import Mathlib
/-Your math friend Steven rolls five fair icosahedral dice (each of which is labelled $1,2, \ldots, 20$ on its sides). He conceals the results but tells you that at least half of the rolls are 20. Suspicious, you examine the first two dice and find that they show 20 and 19 in that order. Assuming that Steven is truthful, what is the probability that all three remaining concealed dice show $20 ?$-/

-- Define the set of possible outcomes for a single 20-sided die roll.
def d20_roll : Finset ℕ := Finset.Icc 1 20

-- The problem reduces to the outcomes of the last three dice.
-- So, our sample space Ω is for three d20 rolls.
def Ω : Finset (ℕ × ℕ × ℕ) :=
  Finset.product d20_roll (Finset.product d20_roll d20_roll)


-- Total outcomes: 20 * 20 * 20 = 8000.
lemma card_Ω : Ω.card = 8000 := by
  simp [Ω, d20_roll, Finset.card_product]
  native_decide

-- Let A be the event that all three dice show 20.
def A : Finset (ℕ × ℕ × ℕ) :=
  Ω.filter (fun ⟨d3, d4, d5⟩ => d3 = 20 ∧ d4 = 20 ∧ d5 = 20)

-- We can easily prove the cardinality of A.
lemma card_A : A.card = 1 := by
  simp [A]
  native_decide

-- Let B be the event that at least two of the three dice show 20.
-- We can define a helper function to count the number of 20s in a triple.
def num_twenties (d3 d4 d5 : ℕ) : ℕ :=
  (if d3 = 20 then 1 else 0) + (if d4 = 20 then 1 else 0) + (if d5 = 20 then 1 else 0)

def B : Finset (ℕ × ℕ × ℕ) :=
  Ω.filter (fun ⟨d3, d4, d5⟩ => num_twenties d3 d4 d5 ≥ 2)

-- To find the cardinality of B, we split it into two disjoint events:
-- B_exactly2: Exactly two dice are 20.
-- B_exactly3: Exactly three dice are 20. (This is the same as event A).
def B_exactly2 : Finset (ℕ × ℕ × ℕ) :=
  Ω.filter (fun ⟨d3, d4, d5⟩ => num_twenties d3 d4 d5 = 2)

def B_exactly3 : Finset (ℕ × ℕ × ℕ) :=
  Ω.filter (fun ⟨d3, d4, d5⟩ => num_twenties d3 d4 d5 = 3)

-- It's clear that B_exactly3 is the same set as A.
lemma B_exactly3_eq_A : B_exactly3 = A := by
  native_decide

-- Let's prove the cardinality of the "exactly two 20s" event.
lemma card_B_exactly2 : B_exactly2.card = 57 := by
  -- We partition B_exactly2 into three disjoint sets based on which die is NOT 20.
  let C₁ := Ω.filter (fun ⟨d3, d4, d5⟩ => d3 ≠ 20 ∧ d4 = 20 ∧ d5 = 20)
  let C₂ := Ω.filter (fun ⟨d3, d4, d5⟩ => d3 = 20 ∧ d4 ≠ 20 ∧ d5 = 20)
  let C₃ := Ω.filter (fun ⟨d3, d4, d5⟩ => d3 = 20 ∧ d4 = 20 ∧ d5 ≠ 20)
  have h_union : B_exactly2 = C₁ ∪ C₂ ∪ C₃ := by native_decide
  have h_disjoint₁₂ : Disjoint C₁ C₂ := by native_decide
  have h_disjoint₁₃ : Disjoint C₁ C₃ := by native_decide
  have h_disjoint₂₃ : Disjoint C₂ C₃ := by native_decide
  have h_card_c1 : C₁.card = 19 := by simp [C₁, d20_roll]; rfl
  have h_card_c2 : C₂.card = 19 := by simp [C₂, d20_roll]; native_decide
  have h_card_c3 : C₃.card = 19 := by simp [C₃, d20_roll]; native_decide
  rw [h_union, Finset.card_union_of_disjoint]
  rw [Finset.card_union_of_disjoint]
  rw[h_card_c1, h_card_c2, h_card_c3]
  exact h_disjoint₁₂
  rw [Finset.disjoint_union_left]
  exact ⟨h_disjoint₁₃,h_disjoint₂₃⟩

theorem card_B : B.card = 58 := by native_decide

-- The final probability is P(A|B) = |A| / |B| since A ⊂ B.
theorem combinatorics_609954 : A.card / (B.card : ℚ)  = 1 / 58 := by
  rw[card_B, card_A]
  norm_cast
