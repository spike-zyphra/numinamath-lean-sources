import Mathlib

/-
Bessie starts at (0,0), wants to reach (5,5), moving only north or east,
and cannot pass through the blocked points: (1,1), (2,3), (3,2).
-/

def isRock : ℕ → ℕ → Bool
  | 1, 1 => true
  | 2, 3 => true
  | 3, 2 => true
  | _, _ => false

partial def numPaths : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | x, y =>
    if isRock x y then 0
    else
      let left := if x > 0 then numPaths (x - 1) y else 0
      let down := if y > 0 then numPaths x (y - 1) else 0
      left + down


#eval numPaths 5 5  

-- Final theorem: the number of valid paths to (5,5) is exactly 32
theorem Combination_611123 : numPaths 5 5 = 32 := by
  native_decide
