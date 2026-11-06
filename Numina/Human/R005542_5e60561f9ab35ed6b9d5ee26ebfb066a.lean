import Mathlib

open List Finset
/-David, Delong, and Justin each showed up to a problem writing session at a random time during the session. If David arrived before Delong, what is the probability that he also arrived before Justin?
-/


-- Define the people
inductive Person : Type
| David | Delong | Justin
deriving DecidableEq, Fintype, Repr

-- List of all people
abbrev all_people : List Person := [Person.David, Person.Delong, Person.Justin]

-- Lemma: all_people has no duplicates
lemma all_people_nodup : all_people.Nodup := by decide

-- Lemma: all_people has length 3
lemma all_people_length : all_people.length = 3 := by rfl

-- The set of all possible arrival orderings (permutations)
def all_orderings : Finset (List Person) := all_people.permutations.toFinset

-- Lemma: Cardinality of all_orderings is 3! = 6
lemma card_all_orderings : all_orderings.card = Nat.factorial 3 := by
  unfold all_orderings
  simp[all_people]
  have : (all_people.permutations).Nodup := by simp[all_people]
  rw [toFinset_card_of_nodup (by assumption)]
  simp[all_people, permutations]
  decide

-- Helper function: checks if p1 appears before p2 in a list (an ordering)
-- Requires that both p1 and p2 are in the list.
def appears_before (p1 p2 : Person) (ordering : List Person)
     : Prop :=
  ordering.indexOf p1 < ordering.indexOf p2

-- Instance for decidability of appears_before
instance appears_before_decidable (p1 p2 : Person) (ordering : List Person):
    Decidable (appears_before p1 p2 ordering ) := by
  unfold appears_before
  exact Nat.decLt _ _

-- Event E1: David arrived before Delong (t_D < t_L)
def event_E1 : Finset (List Person) :=
  all_orderings.filter (fun ordering =>
    appears_before Person.David Person.Delong ordering 
  )

-- Event E2: David arrived before Justin (t_D < t_J)
def event_E2 : Finset (List Person) :=
  all_orderings.filter (fun ordering =>
    appears_before Person.David Person.Justin ordering 
  )

-- Event (E1 ∩ E2): David before Delong AND David before Justin
def event_E1_cap_E2 : Finset (List Person) :=
  event_E1 ∩ event_E2

-- Calculate card(E1)
lemma card_event_E1 : event_E1.card = 3 := by
  -- Enumerate permutations and check the condition
  -- Orderings:
  -- [D,L,J] -> D < L (True)
  -- [D,J,L] -> D < L (True)
  -- [L,D,J] -> D < L (False)
  -- [L,J,D] -> D < L (False)
  -- [J,D,L] -> D < L (True)
  -- [J,L,D] -> D < L (False)
  -- Total 3.
  -- A more general argument: For any pair (X,Y) from 3 distinct items,
  -- X is before Y in exactly half of the permutations. 3! / 2 = 6 / 2 = 3.
  rw [show event_E1.card = (all_orderings.filter (fun p => (indexOf Person.David p < indexOf Person.Delong p))).card by
      native_decide
  ]
  simp[indexOf, all_orderings,all_people, permutations]
  decide
  -- We can list the elements explicitly.
  

-- Calculate card(E1 ∩ E2)
lemma card_event_E1_cap_E2 : event_E1_cap_E2.card = 2 := by
  -- E1 ∩ E2 means D < L AND D < J. This means D is the first of the three.
  -- The other two (L, J) can be in any order (L,J) or (J,L).
  -- So, [D,L,J] and [D,J,L]. Total 2.
  have h_elements : ∀ p ∈ event_E1,
    p ∈ event_E2 ↔
    (p = [Person.David, Person.Delong, Person.Justin] ∨
     p = [Person.David, Person.Justin, Person.Delong]) := by
    intro p hp_E1
    simp [event_E1, mem_filter] at hp_E1
    rcases hp_E1 with ⟨hp_all, h_D_lt_L_prop⟩
    constructor
    intro h 
    simp [event_E2, appears_before, all_orderings ,all_people, permutations] at h 
    
    simp [appears_before] at h_D_lt_L_prop
    rcases h with ⟨h | h | h | h | h | h, h1⟩ <;> simp [h] <;> simp [h] at h_D_lt_L_prop 
    simp [h] at h1
    intro h 
    simp [event_E2, appears_before, all_orderings ,all_people, permutations] 

    rcases h with h | h <;>
    simp[h]

  norm_num [card_event_E1, event_E1_cap_E2, event_E2, appears_before]
  native_decide

-- The conditional probability P(E2 | E1) = card(E1 ∩ E2) / card(E1)
def final_probability : ℚ :=
  (↑(event_E1_cap_E2.card ) : ℚ) / (↑(event_E1.card) : ℚ)

-- Theorem stating the final calculated probability
theorem combinatorics_608741 :
    final_probability = (2 : ℚ) / 3 := by
  unfold final_probability
  rw [card_event_E1_cap_E2, card_event_E1]
  norm_cast 

