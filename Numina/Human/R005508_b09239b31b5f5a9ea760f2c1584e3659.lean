import Mathlib

open Int

-- Define all valid next states from a given state
def factorialMoves (x : ℤ) : List ℤ :=
  (List.range' 1 6).flatMap (λ n => [x + n.factorial, x - n.factorial])

-- After n steps starting from initial states
def reachablePathsInNSteps : ℕ → List (List ℤ)
| 0 => [[0]]
| n + 1 =>
  let prev := reachablePathsInNSteps n
  prev.flatMap (λ path =>
    let last := path.head!
    factorialMoves last |>.map (λ next => next :: path))

-- Number of ways to reach a target number after n steps
def numberOfWays (target : ℤ) (steps : ℕ) : ℕ :=
  let isValid (path : List ℤ) : Bool := path.head! = target
  (reachablePathsInNSteps steps).countP (λ path => isValid path)

theorem combinatorics_608571 : numberOfWays 100 4 = 36 := by
  native_decide
--It's non-trivial to express the statment and follow the infomral analytical argument, so the best I can do here is model all the possible states and brute force