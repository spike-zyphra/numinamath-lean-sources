import Mathlib

theorem algebra_456 : let f := fun (x : ℤ) => if x % 3 = 0 ∧ x % 7 = 0 then x / 21 else if x % 7 = 0 then 3 * x else if x % 3 = 0 then 7 * x else x + 3
IsLeast {a | 1 < a ∧ f 2 = f^[a] 2} 7 := by 
  constructor 
  · -- Show that 7 belongs to the set 
    constructor
    · norm_num
    · native_decide
  · -- Show that 7 is the least element in the set
    intro a ha
    rcases ha with ⟨ha1, ha2⟩
    by_contra h
    push_neg at h
    interval_cases a <;> try { contradiction }
    <;> try { native_decide }