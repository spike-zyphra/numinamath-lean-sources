import Mathlib

theorem algebra_155560 {x y z : ℤ} (h : ({z, y, x} : Multiset ℤ) = {z ^ 2, y + 1, x - 1}) (h' : x + y + z = 2013) :
    x = 1007 ∧ y = 1006 ∧ z = 0 := by
  have h1 : x + y + z = (x - 1) + (y + 1) + z ^ 2 := by
    calc
      _ = ({z, y, x} : Multiset ℤ).sum := by simp; ring
      _ = ({z ^ 2, y + 1, x - 1} : Multiset ℤ).sum := by congr
      _ = _ := by simp; ring

  have h2 : z = z ^ 2 := by
    have eq1 : (x + y + z : ℤ) = (x + y + z ^ 2 : ℤ) := by
      linarith
    have eq2 : z = z ^ 2 := by 
      linarith 
    exact_mod_cast eq2

  have h3 : x = y + 1 := by 
    rw [← h2] at h 
    simp at h 
    rw [Multiset.cons_eq_cons] at h 
    obtain ⟨hx, h⟩ | ⟨hx, ⟨cs, hcs, hcs'⟩⟩ := h 
    · linarith only [hx] 
    · simp at hcs 
      exact hcs.1

  have h4 : z * (z - 1) = 0 := by
    nlinarith

  have h5 : z = 0 ∨ z = 1 := by
    cases (mul_eq_zero.1 h4) with
    | inl h6 =>
      left 
      linarith
    | inr h7 =>
      right 
      linarith
  rcases h5 with (hz0 | hz1)
  · -- Case z = 0. 
    have eq1 : x + y = 2013 := by 
      nlinarith [h', hz0]
    have eq2 : x = 1007 := by 
      rw [h3] at eq1 
      omega 
    have eq3 : y = 1006 := by 
      omega 
    exact ⟨by linarith, by linarith, by linarith⟩ 
  · -- Case z = 1. 
    have hz1 : z = 1 := hz1
    have eq1 : x + y = 2012 := by 
      nlinarith [h', hz1]
    rw [h3] at eq1 
    have eq2 : 2 * y = 2011 := by 
      linarith 
    have eq3 : 2 * y ≠ 2011 := by 
      omega 
    exfalso 
    exact eq3 eq2