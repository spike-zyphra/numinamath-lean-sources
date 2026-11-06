import Mathlib
/-Three fair six-sided dice, each numbered 1 through 6 , are rolled. What is the probability that the three numbers that come up can form the sides of a triangle?-/

-- Define the set of possible outcomes for a single die roll.
def die_roll : Finset ℕ := Finset.Icc 1 6

-- Define the sample space Ω for rolling three dice. It's the cartesian product
-- of three die rolls. We represent an outcome as a triple (x, y, z).
def Ω : Finset (ℕ × ℕ × ℕ) :=
  Finset.product die_roll (Finset.product die_roll die_roll)

-- The total number of possible outcomes is 6*6*6 = 216.
lemma card_Ω : Ω.card = 216 := by
  simp [Ω, die_roll, Finset.card_product]
  rfl

-- The three numbers (x, y, z) can form a triangle if they satisfy the
-- triangle inequality.
def forms_triangle (x y z : ℕ) : Prop :=
  x + y > z ∧ x + z > y ∧ y + z > x
instance : DecidablePred fun x =>
    match x with
    | (x, y, z) => forms_triangle x y z := by
    unfold forms_triangle
    infer_instance

-- The event `E` is the set of outcomes that can form a triangle.
def E : Finset (ℕ × ℕ × ℕ) :=
  Ω.filter (fun ⟨x, y, z⟩ => forms_triangle x y z)

-- The complement event `F` is the set of outcomes that cannot form a triangle.
def F : Finset (ℕ × ℕ × ℕ) :=
  Ω.filter (fun ⟨x, y, z⟩ => ¬(forms_triangle x y z))

-- The failure condition `¬(forms_triangle x y z)` is equivalent to
-- `y + z ≤ x ∨ x + z ≤ y ∨ x + y ≤ z`.
-- We define three sets for each of these disjoint conditions.
def F₁ : Finset (ℕ × ℕ × ℕ) := Ω.filter (fun ⟨x, y, z⟩ => y + z ≤ x)
def F₂ : Finset (ℕ × ℕ × ℕ) := Ω.filter (fun ⟨x, y, z⟩ => x + z ≤ y)
def F₃ : Finset (ℕ × ℕ × ℕ) := Ω.filter (fun ⟨x, y, z⟩ => x + y ≤ z)

-- We prove that these three failure sets are pairwise disjoint.
lemma f_disjoint :Disjoint F₁ F₂ ∧ Disjoint F₁ F₃ ∧ Disjoint F₂ F₃ := by decide
-- The proof is based on the fact that if, e.g., y+z ≤ x and x+z ≤ y,
-- then y < x and x < y (since z ≥ 1), which is a contradiction.

-- We also prove that the union of these three sets is the total failure set F.
lemma f_union : F = F₁ ∪ F₂ ∪ F₃ := by
  native_decide

lemma card_F₁ : F₁.card = 35 := by decide
lemma card_F₂ : F₂.card = 35 := by decide
lemma card_F₃ : F₃.card = 35 := by decide

-- The cardinality of the total failure set F is the sum of the cardinalities
-- of the disjoint sets F₁, F₂, and F₃.
lemma card_F : F.card = 105 := by
  rw [f_union]
  rw [Finset.card_union_of_disjoint]
  rw [Finset.card_union_of_disjoint]
  rw[card_F₁, card_F₂, card_F₃] 
  exact f_disjoint.1
  exact Finset.disjoint_union_left.mpr ⟨f_disjoint.2.1, f_disjoint.2.2⟩ 

-- The number of successful outcomes is the total number of outcomes minus
-- the number of failure outcomes.
theorem card_E : E.card = 111 := by decide

-- The final probability is the ratio of successful outcomes to the total number of outcomes.
-- 111 / 216 simplifies to 37 / 72.
theorem combinatorics_611328 : (E.card : ℚ) / Ω.card = 37 / 72 := by
norm_cast
rw[card_E, card_Ω]
ring
