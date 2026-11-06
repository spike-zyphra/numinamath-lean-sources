import Mathlib

/- According to the standard convention for exponentiation, 2^2^2^2 = 2^(2^(2^2)) = 2^16=65536.
If the order in which the exponentiations are performed is changed, how many other values are possible?
(A) 0(B) 1(C) 2(D) 3(E) 4 -/
theorem algebra_94161 : {x| (x = 2^(2^(2^2)) ∨ x = 2^((2^2)^2) ∨ x = ((2^2)^2)^2 ∨ x = (2^(2^2))^2 ∨ x = (2^2)^(2^2)) ∧ x ≠ 65536 }.encard = 1 := by
  simp
  --show that the set containing all disposition of the parenteses but result ≠ 65536 is {256}
  have h : {x | (x = 65536 ∨ x = 256) ∧ ¬x = 65536} = {256} := by 
    ext x
    simp
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      obtain k1|k2 := h1
      · contradiction
      · exact k2
    · intro h
      refine or_and_right.mpr ?h.mpr.a
      right
      constructor
      · exact h
      · rw[h]
        push_neg
        linarith
  --with the above hypotheses is clear thart the cardinality of the set is 1
  rw[h]
  simp