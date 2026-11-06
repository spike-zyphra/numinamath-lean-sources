import Mathlib
open Nat Finset Fintype

/-How many functions $f:\{1,2,3,4,5\} \rightarrow\{1,2,3,4,5\}$ have the property that $f(\{1,2,3\})$ and $f(f(\{1,2,3\}))$ are disjoint?-/

abbrev Domain := Fin 5

-- The function f maps from {0..4} to {0..4}.
abbrev F := Domain → Domain

-- Let S₀ be the set {1,2,3}, represented by {0,1,2} in Fin 5.
def S₀ : Finset Domain := {0, 1, 2}

-- A function `f` has the property if f({0,1,2}) and f(f({0,1,2})) are disjoint.
def has_property (f : F) : Prop :=
  let A := S₀.image f
  let f_A := A.image f
  Disjoint A f_A

instance : DecidablePred has_property := by unfold has_property; infer_instance

-- The set of all functions that have the property.
def P : Finset F := univ.filter has_property

-- Lemma: If a function f has the property, its image of S₀ must be disjoint from S₀.
lemma image_of_S0_disjoint_S0 (f : F) (h_prop : has_property f) :
  Disjoint (S₀.image f) S₀ :=
by
  -- Proof by contradiction: Assume there is an element y in both sets.
  unfold Disjoint
  simp [eq_empty_iff_forall_not_mem]
  intro y h1 h2 x
  simp[has_property] at h_prop
  by_contra!

  -- simp[Disjoint]at h_prop
  -- specialize h_prop h1 
  -- simp [subset_iff] at h_prop 
  -- have : (∀ ⦃x : Domain⦄, x ∈ y → ∃ a ∈ S₀, f (f a) = x) := by 
  --   intros x hx 
  --   have h1 := mem_of_subset h1 hx
  --   -- have h2 := mem_of_subset h2 hx
  --   simp at h1
  --   obtain ⟨a, ha⟩ := h1 
  --   use a
    -- simp[ha]
  replace h1 := mem_of_subset h1 this
  replace h2 := mem_of_subset h2 this
  have h3 : f x ∈ S₀.image f := mem_image_of_mem f h2
  have h4 : f x ∈ (S₀.image f).image f := mem_image_of_mem f h1

  rw [disjoint_right] at h_prop
  have := h_prop h4
  simp_all

-- This lemma implies that for any valid f, f(S₀) must be a subset of S₀'s complement.
-- In Fin 5, S₀ = {0,1,2}, so S₀.compl = {3,4}.
-- Thus, f(S₀) must be a subset of {3,4}.

-- Theorem: The number of functions with the property is 94.
theorem combinatorics_608691 : P.card = 94 :=
by
  unfold P has_property
  simp
  native_decide
