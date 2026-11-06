import Mathlib

theorem algebra_5913 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b + c = 100) (h2 : ∀ x : ℤ, Odd x → Odd (a * x ^ 2 + b * x + c))
    (h3 : ∀ x : ℤ, Odd x → ¬(a * x ^ 2 + b * x + c = x / 4)) :
    (∑ i in Finset.Icc 1 10, {x | ∃ n : ℤ, x = a * n ^ 2 + b * n + c}.ncard) % 1000 = 587 := by 
  have h4 : (a + b + c : ℤ) = 100 := by exact_mod_cast h1
  have fact2 := h2 1 (by decide)
  have h7 : (a + b + c : ℤ) = 100 := h4
  have h8 : Odd ((a : ℤ) + (b : ℤ) + (c : ℤ)) := by 
    simpa using fact2
  have h9 : (a + b + c : ℤ) % 2 = 1 := by 
    obtain ⟨k, hk⟩ := h8
    omega
  -- This leads to a contradiction because a + b + c = 100 is even
  have h11 : (a + b + c : ℤ) % 2 = 0 := by 
    omega 
  omega