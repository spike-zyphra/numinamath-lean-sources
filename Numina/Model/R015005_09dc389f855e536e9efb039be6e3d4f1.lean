import Mathlib

theorem number_theory_61102 (A B C : ℤ × ℤ)
    (h₀ : ∃ a b c : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧
      dist B C = a ∧ dist A C = b ∧ dist A B = c) :
    Even (dist B C + dist A C + dist A B) := by 
  rcases h₀ with ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩
  rw [h1, h2, h3]
  have h4 : a > 0 := ha
  have h5 : b > 0 := hb
  have h6 : c > 0 := hc
  simp [dist, even_iff_two_dvd] at *
  <;> ring_nf 
  <;> norm_num
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { tauto }
  <;> try { nlinarith }