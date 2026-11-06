import Mathlib

def f (n : ℕ) := n - (Nat.digits 10 n).sum

theorem number_theory_218087 :
    {n | f^[11] n = 0 ∧ n ≥ 100 ∧ n ≤ 109} = {100, 101, 102, 103, 104, 105, 106, 107, 108, 109} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume f^[11] n = 0 ∧ n ≥ 100 ∧ n ≤ 109, prove n ∈ {100, ..., 109}
    intro h
    rcases h with ⟨h1, h2, h3⟩
    interval_cases n <;> norm_num [f, Function.iterate_succ_apply'] at h1 ⊢ <;> tauto
  · -- Assume n ∈ {100, ..., 109}, prove f^[11] n = 0 ∧ n ≥ 100 ∧ n ≤ 109
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · constructor
      · norm_num [f, Function.iterate_succ_apply']
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num [f, Function.iterate_succ_apply']
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num [f, Function.iterate_succ_apply']
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num [f, Function.iterate_succ_apply']
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num [f, Function.iterate_succ_apply']
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num [f, Function.iterate_succ_apply']
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num [f, Function.iterate_succ_apply']
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num [f, Function.iterate_succ_apply']
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num [f, Function.iterate_succ_apply']
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num [f, Function.iterate_succ_apply']
      constructor
      · norm_num
      · norm_num