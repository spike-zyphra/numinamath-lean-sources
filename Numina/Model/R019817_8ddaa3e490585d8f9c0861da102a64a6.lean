import Mathlib

theorem number_theory_119512 :
    Set.Infinite {(a, b, c) : ℕ × ℕ × ℕ | a ^ 15 + b ^ 15 = c ^ 16} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => (2^(1 + 16*t), 2^(1 + 16*t), 2^(1 + 15*t)))
  · -- Show f is injective
    intro t s h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that for all t, f(t) is in the set
    intro t
    simp [Prod.ext_iff]
    have h15 : ((2 : ℕ) ^ (1 + 16 * t)) ^ 15 + ((2 : ℕ) ^ (1 + 16 * t)) ^ 15 = ((2 : ℕ) ^ (1 + 15 * t)) ^ 16 := by
      ring_nf
    exact h15