import Mathlib

/-
Compute the number of ways to pick a 3 -element subset of

$$
\left\{10^{1}+1,10^{2}+1,10^{3}+1,10^{4}+1,10^{5}+1,10^{6}+1,10^{7}+1\right\}
$$

such that the product of the 3 numbers in the subset has no digits besides 0 and 1 when written in base 10 .
-/

def mySet : Finset ℕ :=
  List.toFinset [10^1 + 1, 10^2 + 1, 10^3 + 1, 10^4 + 1, 10^5 + 1, 10^6 + 1, 10^7 + 1]

-- Property that a number's digits are only 0 or 1
def property (n : ℕ) : Prop :=
  ∀ i : Fin (Nat.digits 10 n).length, ((Nat.digits 10 n).get i = 0 ∨ (Nat.digits 10 n).get i = 1 )

-- Instance to show that `property n` is Decidable.
-- This is needed for `Finset.filter` to work with predicates involving `property`.
instance decidableProperty (n : ℕ) : Decidable (property n) := by
  unfold property 
  apply Nat.decidableForallFin

-- The combined predicate for the subtype.
-- A Finset `subset` satisfies this if:
-- 1. It's a subset of `mySet`.
-- 2. Its cardinality is 3.
-- 3. The product of its elements satisfies our `property`.
def mainPredicate (subset : Finset ℕ) : Prop :=
  subset ⊆ mySet ∧ subset.card = 3 ∧ property (subset.prod id)

-- Instance to show that `mainPredicate subset` is Decidable.
-- This is also needed for `Finset.filter`.
instance decidableMainPredicate (subset : Finset ℕ) : Decidable (mainPredicate subset) := by
  unfold mainPredicate
  infer_instance

-- Define the actual Finset of subsets that satisfy `mainPredicate`.
-- This is the set whose cardinality is the solution to the original problem.
def solutionFinset : Finset (Finset ℕ) :=
  -- Start with all subsets of `mySet`
  mySet.powerset.filter mainPredicate

-- Now, define the Fintype instance for the subtype.
instance myFintype : Fintype {subset : Finset ℕ // mainPredicate subset} :=
  -- `Fintype.ofFinset` constructs a Fintype instance from a finset and a proof.
  Fintype.ofFinset solutionFinset (fun S => by
    simp only [solutionFinset, Finset.mem_filter, Finset.mem_powerset]
    simp only [mainPredicate]
    constructor
    intro h
    exact ⟨h.1, h.2.2⟩
    intro h
    exact ⟨h.1, h.1, h.2⟩
  )

theorem number_theory_610776 : solutionFinset.card = 26 := by native_decide