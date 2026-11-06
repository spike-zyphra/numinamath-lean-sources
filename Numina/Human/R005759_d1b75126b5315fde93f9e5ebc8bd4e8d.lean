import Mathlib
open Nat Finset 

-- 1. Representing Bases and Strands

-- Define the set of bases
inductive Base : Type where
  | H : Base
  | M : Base
  | N : Base
  | T : Base
deriving DecidableEq, Fintype

-- Define a Strand as a list of 5 bases
abbrev Strand := List Base

-- Define a DNA sequence as a list of 5 base pairs
abbrev DNA := List.Vector (Base × Base) 5
instance Fintype_DNA : Fintype DNA := by
  dsimp[DNA]
  infer_instance
-- 2. Defining Constraints

-- Predicate for distinct bases in a pair
def distinct_bases : Base × Base → Prop :=
  fun (b1, b2) => b1 ≠ b2

-- Predicate for avoiding H-M and N-T adjacency on a strand
def valid_strand (s : Strand) : Prop :=
  ∀ i : Fin s.length,
    ∀ j : Fin s.length,
      i.val + 1 = j.val →
      ¬((s.get i == Base.H ∧ s.get j == Base.M) ∨
        (s.get i == Base.M ∧ s.get j == Base.H) ∨
        (s.get i == Base.N ∧ s.get j == Base.T) ∨
        (s.get i == Base.T ∧ s.get j == Base.N))

-- Predicate for a valid DNA sequence
def valid_dna (dna : DNA) : Prop :=
  (∀ bp ∈ dna.val, distinct_bases bp) ∧
  let strand1 := dna.val.map Prod.fst
  let strand2 := dna.val.map Prod.snd
  valid_strand strand1 ∧ valid_strand strand2

instance valid_dna_decidable : DecidablePred valid_dna :=
  fun dna => by
    -- This will require checking the length and distinctness of pairs
    -- and validating the strands.
    unfold valid_dna valid_strand distinct_bases
    infer_instance
-- 3. Counting Valid Sequences

-- Function to generate all possible DNA sequences
def all_dna_sequences : Finset DNA := Finset.univ -- Formalize generating all lists of 5 pairs of bases

-- Function to filter out invalid sequences
def valid_dna_sequences : Finset DNA :=
  all_dna_sequences.filter valid_dna

-- Theorem: The number of valid DNA sequences is 28812
theorem count_valid_dna_sequences :
  valid_dna_sequences.card = 28812 := by
  unfold valid_dna_sequences valid_dna all_dna_sequences distinct_bases valid_strand
  native_decide
