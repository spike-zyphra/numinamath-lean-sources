import Mathlib

theorem number_theory_59223 :
    IsLeast {n | ∀ a ∈ Finset.Icc 2 10, n ≡ (a - 1) [MOD a]} 2519 := by
  constructor
  · -- Show 2519 is in the set
    intro a ha
    rw [Finset.mem_Icc] at ha
    rcases ha with ⟨ha2, ha10⟩
    interval_cases a <;> native_decide
  · -- Show there is no smaller element in the set
    intro n hn
    have h2 := hn 2 (by norm_num)
    have h3 := hn 3 (by norm_num)
    have h4 := hn 4 (by norm_num)
    have h5 := hn 5 (by norm_num)
    have h6 := hn 6 (by norm_num)
    have h7 := hn 7 (by norm_num)
    have h8 := hn 8 (by norm_num)
    have h9 := hn 9 (by norm_num)
    have h10 := hn 10 (by norm_num)
    norm_num [Nat.ModEq] at h2 h3 h4 h5 h6 h7 h8 h9 h10
    by_contra h
    push_neg at h
    interval_cases n <;> omega