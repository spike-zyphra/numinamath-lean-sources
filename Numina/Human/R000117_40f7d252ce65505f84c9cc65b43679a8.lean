import Mathlib

def answer:Finset Nat:= {1,3,5,7,9,11}

theorem formal_2919_t(x y:ℕ)(h1:x%13≠y%13)(h2:Odd (x%13))(h3: Odd (y%13)) : (x%13) ∈ answer := by
  have h11:x%13<13:= by
    exact Nat.mod_lt x (by norm_num)
  have h12:y%13<13:= by
    exact Nat.mod_lt y (by norm_num)
  generalize eq1:x%13 = a
  generalize eq2:y%13 = b
  rw [eq1] at h11 h2
  rw [eq2] at h12 h3
  interval_cases a
  any_goals simp [answer]
  any_goals trivial

theorem formal_2919(x y:ℕ)(h1:x%13≠y%13)(h2:Odd (x%13))(h3: Odd (y%13)) : ((x%13) ∈ answer) ∧  ((y%13) ∈ answer) := by
constructor
exact formal_2919_t x y h1 h2 h3
apply formal_2919_t y x
symm
exact h1
exact h3
exact h2

