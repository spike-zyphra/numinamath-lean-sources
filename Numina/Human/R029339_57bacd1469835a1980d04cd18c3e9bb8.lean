import Mathlib

set_option maxHeartbeats 10000000

theorem number_theory_205510 : IsLeast {n | 0 < n ∧ (Nat.digits 10 (2007 * n)).take 3 = [7, 3, 8]} 691 := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    native_decide
  · intro n hn
    have ⟨hnpos, hndig⟩ := hn
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hndig