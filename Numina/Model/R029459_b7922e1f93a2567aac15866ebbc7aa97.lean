import Mathlib

theorem number_theory_92110 (a b c : ℕ) (ha : a ∈ Finset.Icc 100 999) (hb : b ∈ Finset.Icc 100 999)
    (hc : c ∈ Finset.Icc 100 999) (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) (h1 : (Nat.digits 10 a).length = 3)
    (h2 : (Nat.digits 10 b).length = 3) (h3 : (Nat.digits 10 c).length = 3) (h4 : (Nat.digits 10 a).toFinset.card = 3)
    (h5 : (Nat.digits 10 b).toFinset.card = 3) (h6 : (Nat.digits 10 c).toFinset.card = 3)
    (h7 : (Nat.digits 10 a).toFinset ∪ (Nat.digits 10 b).toFinset ∪ (Nat.digits 10 c).toFinset = Finset.Icc 1 9)
    (h8 : a * 3 = b * 1 ∧ b * 5 = c * 3) :
    a = 129 ∧ b = 387 ∧ c = 645 := by
  rw [Finset.mem_Icc] at ha hb hc 
  rcases ha with ⟨ha1, ha2⟩ 
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  have h9 : a * 3 = b * 1 := h8.1 
  have h10 : b * 5 = c * 3 := h8.2 
  have h11 : b = 3 * a := by
    linarith
  have h12 : c = 5 * a := by
    nlinarith [h11, h10]
  have h13 : a ≤ 199 := by
    nlinarith [h12, hc2]
  interval_cases a <;> norm_num [h11, h12] at *
  <;> try { contradiction }
  <;> try { tauto }