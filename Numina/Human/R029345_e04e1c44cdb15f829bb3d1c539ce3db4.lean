import Mathlib

theorem number_theory_229320 : IsGreatest {x | ∃ n, x = 2015 % n ∧ 1 ≤ n ∧ n ≤ 1000} 671 := by
  refine' ⟨by use 672; norm_num, fun x hx => _⟩
  rcases hx with ⟨n, rfl, hn1, hn2⟩
  norm_num
  interval_cases n <;> norm_num