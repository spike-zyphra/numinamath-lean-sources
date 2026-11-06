import Mathlib

/- Which of the following integers are divisible by 3? Of those that are, which are divisible by 9?
a) 18381
b) 65412351
c) 987654321
d) 78918239735-/
theorem number_theory_4745 :
    (3 ∣ 18381 ∧ ¬9 ∣ 18381) ∧
    (3 ∣ 65412351 ∧ 9 ∣ 65412351) ∧
    (3 ∣ 987654321 ∧ 9 ∣ 987654321) ∧
    ¬(3 ∣ 78918239735) := by
  -- verify by computation
  native_decide
