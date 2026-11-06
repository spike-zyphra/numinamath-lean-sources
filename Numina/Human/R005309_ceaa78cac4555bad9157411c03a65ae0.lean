import Mathlib

def point := ℕ × ℕ

def path := List point

-- All the path start from p.
def allPath (px : ℕ) : ℕ → List path
| 0 => [[(0,0)]]
| py + 1 =>
  let go := if px = 7 then
      [px - 1]
    else if px = 0 then
      [px + 1]
    else
      [px - 1, px + 1];
  do
    let next ← go
    let pa ← allPath next py
    return ((px, py + 1) :: pa)

-- Count from top to bottom, so that we can pass termination check
theorem Combinatorics_607544 : (allPath 0 7).length + (allPath 2 7).length + (allPath 4 7).length + (allPath 6 7).length = 296 := by
  native_decide
