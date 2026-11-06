import Mathlib

theorem algebra_79601 : ¬ ∀ p : Polynomial ℤ, ∃ q r : Polynomial ℤ, p = q^3 + r^3 := by

  intro h
  have h1 := h (3)
  rcases h1 with ⟨q, r, h_eq⟩

  have eq1 := congr_arg (fun f => f.eval 0) h_eq
  simp at eq1
  
  have h2 : q.eval 0 ^ 3 + r.eval 0 ^ 3 = 3 := by linarith

  have h3 : q.eval 0 ^ 3 % 9 = 0 ∨ q.eval 0 ^ 3 % 9 = 1 ∨ q.eval 0 ^ 3 % 9 = 8 := by 
    have h4 : q.eval 0 % 9 = 0 ∨ q.eval 0 % 9 = 1 ∨ q.eval 0 % 9 = 2 ∨ q.eval 0 % 9 = 3 ∨ q.eval 0 % 9 = 4 ∨ q.eval 0 % 9 = 5 ∨ q.eval 0 % 9 = 6 ∨ q.eval 0 % 9 = 7 ∨ q.eval 0 % 9 = 8 := by omega
    rcases h4 with (h | h | h | h | h | h | h | h | h) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h] 

  have h4 : r.eval 0 ^ 3 % 9 = 0 ∨ r.eval 0 ^ 3 % 9 = 1 ∨ r.eval 0 ^ 3 % 9 = 8 := by 
    have h5 : r.eval 0 % 9 = 0 ∨ r.eval 0 % 9 = 1 ∨ r.eval 0 % 9 = 2 ∨ r.eval 0 % 9 = 3 ∨ r.eval 0 % 9 = 4 ∨ r.eval 0 % 9 = 5 ∨ r.eval 0 % 9 = 6 ∨ r.eval 0 % 9 = 7 ∨ r.eval 0 % 9 = 8 := by omega
    rcases h5 with (h | h | h | h | h | h | h | h | h) <;> simp [pow_succ, Int.add_emod, Int.mul_emod, h] 

  have h5 : (q.eval 0 ^ 3 + r.eval 0 ^ 3) % 9 = 3 % 9 := by omega

  omega