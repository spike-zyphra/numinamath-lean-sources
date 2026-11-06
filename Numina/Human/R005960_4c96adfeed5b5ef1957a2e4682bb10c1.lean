import Mathlib 

/-Count the number of permutations $a_{1} a_{2} \ldots a_{7}$ of 1234567 with longest decreasing subsequence of length at most two (i.e. there does not exist $i<j<k$ such that $a_{i}>a_{j}>a_{k}$ ).-/

def all_lists := List.permutations (List.range' 1 7)

/-
A function to check if a given list `p` has a decreasing subsequence of length 3.
A decreasing subsequence of length 3 is defined by three indices i < j < k
such that p[i] > p[j] > p[k].
-/
def has_decreasing_subsequence_of_length_three (p : List ℕ) : Bool :=
  let n := p.length
  if n < 3 then false else
  -- Create a list of indices [0, 1, ..., n-1] of type List (Fin n)
  let indices : List (Fin n) := List.finRange n
  -- Check for any triple of indices (i, j, k)
  indices.any fun i =>
    indices.any fun j =>
      indices.any fun k =>
        -- such that i < j < k
        (i < j && j < k &&
        -- and p[i] > p[j] > p[k]
        -- Note: p.get i requires `i : Fin p.length`. This is true for elements from `List.finRange n`.
        let val_i := p.get i
        let val_j := p.get j
        let val_k := p.get k
        val_i > val_j && val_j > val_k)

-- Filter the permutations: we want those that *do not* have a decreasing subsequence of length 3.
-- The condition for keeping a list `p` is that `has_decreasing_subsequence_of_length_three p` is false.

def satisfying_lists : List (List ℕ) :=
  all_lists.filter (fun p => !(has_decreasing_subsequence_of_length_three p))

theorem combinatorics_610921:  satisfying_lists.length = 429 := by native_decide