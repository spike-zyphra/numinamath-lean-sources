import Mathlib

theorem number_theory_4714 (a b c d : ℤ) (hac : a ≠ 0 ∧ c ≠ 0) (hab : a ∣ b) (hcd : c ∣ d) : a * c ∣ b * d := by
  rcases hac with ⟨ha, hc⟩
  rcases hab with ⟨k, hk⟩
  rcases hcd with ⟨m, hm⟩
  use k * m
  rw [show b = a * k by linarith [hk]]
  rw [show d = c * m by linarith [hm]]
  ring_nf
  <;> try tauto
  <;> try ring_nf
  <;> try tauto
  <;> try ring_nf
  <;> try tauto