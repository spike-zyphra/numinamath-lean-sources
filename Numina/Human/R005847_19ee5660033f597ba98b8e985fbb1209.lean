import Mathlib

-- Define the type for positions (indices from 0 to 9)
abbrev Pos := Fin 10

-- Function to map a starting position to the five consecutive positions on the circle
-- (modulo 10 to wrap around the circle)
def consecutiveFive (p : Pos) : Finset Pos :=
  Finset.image (λ i => ⟨(p.val + i) % 10, Nat.mod_lt _ (by decide)⟩) (Finset.range 5)

-- Boolean predicate: checks if there exists some position x ∈ {0..9}
-- that is not included in any of the 4 people's 5-consecutive choices
def missesSomeBool (choices : Fin 4 → Pos) : Bool :=
  (List.finRange 10).any (λ x =>
    (List.finRange 4).all (λ i =>
      ⟨x, by simp⟩ ∉ consecutiveFive (choices ⟨i, by simp⟩)))

-- Executable function to count valid configurations
-- A configuration consists of 4 choices (one for each person), each being a starting position
-- This generates all 10^4 = 10000 possible such 4-tuples of starting indices
-- Then filters for those configurations where some number is missed by all four people
def countConfigurations : ℕ :=
  let indices : List (Fin 10) := List.finRange 10
  let allChoices :=
    (List.product (List.product (List.product indices indices) indices) indices).map (fun (((a, b), c), d) =>
      let f : Fin 4 → Pos := fun
        | 0 => a
        | 1 => b
        | 2 => c
        | 3 => d
      f)
  allChoices.filter missesSomeBool |>.length

-- Final computation: number of configurations where at least one number is missed
-- Answer expected: 3690
theorem combinatroics_610234 : countConfigurations = 3690 := by
  native_decide