import Mathlib

/- A positive integer is called jubilant if the number of 1's in its binary representation is even. For example, $6=110_{2}$ is a jubilant number. What is the 2009th smallest jubilant number? -/
theorem number_theory_250507 :
    (Nat.nth (fun n => n > 0 ∧ Even (Nat.digits 2 n).sum) 2008) = 4018 := by
  -- We show that there are 2008 numbers less than 4018 that are jubilant.
  -- This can be done by `native_decide` because the set is finite.
  have h₁ : Nat.count (fun n => n > 0 ∧ Even (Nat.digits 2 n).sum) 4018 = 2008 := by native_decide
  -- We show that 4018 is a jubilant number.
  have h₂ : (fun n => n > 0 ∧ Even (Nat.digits 2 n).sum) 4018 := by
    simp [show Even 8 from ⟨4, rfl⟩]
  -- Now we use `Nat.nth_count` to get the result.
  have H := Nat.nth_count (p := fun n => n > 0 ∧ Even (Nat.digits 2 n).sum) h₂
  rwa [h₁] at H
