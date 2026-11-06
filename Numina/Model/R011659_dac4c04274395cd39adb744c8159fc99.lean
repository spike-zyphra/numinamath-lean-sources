import Mathlib

theorem number_theory_268728 (a b c : ℕ) (ha : a ∈ Finset.Icc 10 99) 
  (hb : b ∈ Finset.Icc 10 99) (hc : c ∈ Finset.Icc 10 99) 
  (h : a * b * c = 636405) (hab : a ≤ b) (hbc : b ≤ c):
  a + b + c = 259 := by
  rw [Finset.mem_Icc] at ha hb hc
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with  ⟨hb1, hb2⟩
  rcases hc with  ⟨hc1, hc2⟩
  interval_cases a <;> try { 
    omega 
  } <;> try { 
    interval_cases b <;> omega 
  } <;> try { 
    interval_cases c <;> omega 
  }