import Mathlib
open Real

theorem algebra_8196
    {f : ℚ → ℚ}
    (hf : ∀ a, f a = (1 + a) / (1 - a))
    (a : ℕ → ℚ)
    (ha0 : a 0 = 1 / 2)
    (h : ∀ i, a (i + 1) = f (a i)) :
    a 2011 = -1 / 3 := by
  have ha1 : a 1 = 3 := by
    rw [h 0, hf, ha0]
    norm_num
  have ha2 : a 2 = -2 := by
    rw [h 1, hf, ha1]
    norm_num
  have ha3 : a 3 = -1 / 3 := by 
    rw [h 2, hf, ha2]
    norm_num
  have ha4 : a 4 = 1 / 2 := by
    rw [h 3, hf, ha3]
    norm_num
  have h1 : ∀ k : ℕ, a (4 * k + 3) = -1 / 3 := by
    intro k
    induction k with
    | zero =>
      norm_num [ha3]
    | succ k ih =>
      have h2 : a (4 * (k + 1) + 3) = -1 / 3 := by
        have eq1 : a (4 * (k + 1) + 3) = a (4 * k + 7) := by
          ring_nf
        rw [eq1]
        have eq2 : a (4 * k + 7) = f (a (4 * k + 6)) := by
          specialize h (4 * k + 6)
          simpa using h
        have eq3 : a (4 * k + 6) = f (a (4 * k + 5)) := by
          specialize h (4 * k + 5)
          simpa using h
        have eq4 : a (4 * k + 5) = f (a (4 * k + 4)) := by
          specialize h (4 * k + 4)
          simpa using h
        have eq5 : a (4 * k + 4) = f (a (4 * k + 3)) := by
          specialize h (4 * k + 3)
          simpa using h
        rw [eq2, eq3, eq4, eq5, hf, hf, hf, hf, ih]
        <;> norm_num
        <;> field_simp <;> norm_num <;> nlinarith
      simpa using h2
  have h2011 : 2011 = 4 * 502 + 3 := by
    omega
  calc 
    a 2011 = a (4 * 502 + 3) := by rw [h2011]
    _ = -1 / 3 := h1 502