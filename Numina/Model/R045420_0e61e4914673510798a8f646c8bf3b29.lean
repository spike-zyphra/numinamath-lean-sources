import Mathlib

theorem algebra_275527 :
  {n : ℕ | n > 0 ∧ n^2 + 39 = (n + 1)^2 - 50} = {44} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: {n > 0 and n^2 + 39 = (n + 1) ^2 - 50} → {44}
    intro h
    rcases h with ⟨hn1, heq⟩
    have eq1 : n^2 + 39 + 50 = (n + 1)^2 := by
      omega
    have eq2 : n = 44 := by
      nlinarith
    exact eq2
  · -- Second direction: {44} → {n > 0 and n^2 + 39 = (n +1)^2 -50}
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num