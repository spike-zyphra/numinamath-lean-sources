import Mathlib

theorem number_theory_202627 : {x | ∃ n, x = n ∧ (2^13 + 1) * (2^14 + 1) * (2^15 + 1) * (2^16 + 1) % 10 = x} = {5} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the left side, so there exists some n where x = n and the expression equals x
    rintro ⟨n, hn, h⟩
    rw [hn] at *
    -- The Lean system can compute the expression directly
    norm_num at h ⊢
    omega
  · -- Assume x = 5, prove x is in the left side
    intro h
    rw [h]
    refine ⟨5, rfl, ?_⟩
    norm_num