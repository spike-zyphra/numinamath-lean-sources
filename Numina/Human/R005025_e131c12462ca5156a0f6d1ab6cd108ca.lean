import Mathlib


-- The numbers $1,2, \ldots, 2002$ are written in order on a blackboard. Then the 1 st, 4 th, 7 th, $\ldots$, $3 \mathrm{k}+1$ th, $\ldots$ numbers in the list are erased. Then the 1 st, $4 \mathrm{th}, 7 \mathrm{th}, \ldots 3 \mathrm{k}+1$ th numbers in the remaining list are erased (leaving $3,5,8,9,12, \ldots$ ). This process is carried out repeatedly until there are no numbers left. What is the last number to be erased?

def filterByIndex {α : Type*} (xs : List α) (predicate : ℕ → Bool) : List α :=
  (xs.enum.filter (fun (i, _) => predicate i)).map Prod.snd

def singleErase (xs : List ℕ) : List ℕ :=
  filterByIndex xs (fun i => (i + 1) % 3 ≠ 1)

def getErased (xs : List ℕ) : List ℕ :=
  filterByIndex xs (fun i => (i + 1) % 3 = 1)

partial def eraseProcess (xs : List ℕ) : List ℕ :=
  let rec go (current : List ℕ) (result : List ℕ) : List ℕ :=
    if current.isEmpty then result
    else
      let erased := getErased current
      let remaining := singleErase current
      go remaining (result ++ erased)
  go xs []

theorem number_theory_605114 : (eraseProcess (List.range 2002 |>.map (· + 1))).getLast? = some 1598 := by
  native_decide
