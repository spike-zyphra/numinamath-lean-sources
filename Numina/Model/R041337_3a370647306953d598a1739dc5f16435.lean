import Mathlib

theorem number_theory_118918 :
    ¬∃ a b c : ℕ, a ∈ Finset.Icc 1 9 ∧ b ∈ Finset.Icc 0 9 ∧ c ∈ Finset.Icc 0 9 ∧
      IsSquare ((100 * a + 10 * b + c) + (100 * b + 10 * c + a) + (100 * c + 10 * a + b)) := by
  rintro ⟨a, b, c, ha, hb, hc, h⟩ 
  rw [Finset.mem_Icc] at ha hb hc
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩ 
  have h1 : (100 * a + 10 * b + c) + (100 * b + 10 * c + a) + (100 * c + 10 * a + b) = 111 * (a + b + c) := by 
    omega 
  rw [h1] at h
  rcases h with ⟨r, hr⟩ 
  have h2 : r * r = 111 * (a + b + c) := by 
    nlinarith
  have h5 : a + b + c ≤ 27 := by 
    omega 
  have h5' : a + b + c ≥ 1 := by 
    omega 
  have h3 : r ≤ 55 := by 
    nlinarith [h2, show a + b + c ≤ 27 by omega]
  have h4 : r ≥ 11 := by 
    nlinarith [h2, show a + b + c ≥ 1 by omega]
  interval_cases r <;> omega