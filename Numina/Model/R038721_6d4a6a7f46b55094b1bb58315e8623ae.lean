import Mathlib



theorem algebra_10685 : 
    let E (a b c : ℝ) := a * b ^ 2 + c;
    {a | E a 4 5 = E a 6 7} = {-1 / 10} := by
  intro E 
  ext a 
  simp [E]
  constructor
  · -- Assume $16a + 5 = 36a + 7$, prove $a = -1/10$
    intro h
    linarith
  · -- Assume $a = -1/10$, prove $16a + 5 = 36a + 7$
    intro h
    rw [h]
    norm_num