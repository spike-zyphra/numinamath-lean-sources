import Mathlib

theorem number_theory_226937 {p b : ℕ} (hp : p * 8 + b * 6 = 176) (hb : b % 2 = 0) (hp' : p % 2 = 0)
    (hpb : p ∈ Finset.Icc 10 99) (hbb : b ∈ Finset.Icc 10 99) :
    p = 10 ∧ b = 16 := by
  rw [Finset.mem_Icc] at hpb hbb
  rcases hpb with ⟨hp10, hp99⟩
  rcases hbb with ⟨hb10, hb99⟩
  have h1 : p * 8 + b * 6 = 176 := hp
  have h2 : b % 2 = 0 := hb
  have h3 : p % 2 = 0 := hp'
  have h4 : 10 ≤ p := hp10
  have h5 : p ≤ 99 := hp99
  have h6 : 10 ≤ b := hb10
  have h7 : b ≤ 99 := hb99
  interval_cases p <;> omega