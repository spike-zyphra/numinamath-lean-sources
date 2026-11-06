import Mathlib

theorem algebra_16812 :
  IsGreatest {a*d + b*d + c*d + a*e + b*e + c*e + a*f + b*f + c*f | (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (e : ℕ) (f : ℕ) (h : [a, b, c, d, e, f].Perm [2, 3, 5, 7, 11, 13])} 420 := by 
  constructor
  · -- We will show 420 is in the set
    use 2, 5, 13, 3, 7, 11
    native_decide
  · -- We will show 420 is the greatest element in the set
    intro n hn
    rcases hn with ⟨a, b, c, d, e, f, h, rfl⟩
    have eq1 : a + b + c + d + e + f = 41 := by
      have h' : ([a, b, c, d, e, f] : Multiset ℕ).sum = ([2, 3, 5, 7, 11, 13] : Multiset ℕ).sum := by 
        apply h.sum_eq 
      have : ([2, 3, 5, 7, 11, 13] : Multiset ℕ).sum = 41 := by 
        native_decide 
      have : ([a, b, c, d, e, f] : Multiset ℕ).sum = 41 := by 
        linarith [this, h'] 
      simp [Finset.sum] at this ⊢
      all_goals omega 
    have h3 : a * d + b * d + c * d + a * e + b * e + c * e + a * f + b * f + c * f = (a + b + c) * (d + e + f) := by 
      ring
    have h4 : (a + b + c) * (d + e + f) ≤ 420 := by 
      have h5 : a + b + c + d + e + f = 41 := eq1
      have h5' : d + e + f = 41 - (a + b + c) := by 
        omega 
      rw [h5'] 
      have h6 : a + b + c ≤ 41 := by 
        omega 
      interval_cases h7 : a + b + c <;> omega 
    have n8 : a * d + b * d + c * d + a * e + b * e + c * e + a * f + b * f + c * f ≤ 420 := by 
      rw [h3] 
      linarith [h4] 
    omega