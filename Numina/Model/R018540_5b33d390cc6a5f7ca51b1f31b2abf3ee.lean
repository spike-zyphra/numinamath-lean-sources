import Mathlib

theorem number_theory_121538 :
    IsLeast {n | ∀ i ∈ Finset.Icc 2 10, ∀ j ∈ Finset.Icc 2 10, i ≠ j → n % i ≠ n % j} 1799 := by
  constructor
  · -- Show that 1799 belongs to the set
    intro i hi j hj hineq
    fin_cases hi <;> fin_cases hj <;> norm_num at *
  · -- Show that 1799 is the smallest
    intro n hn
    by_contra h
    push_neg at h
    have h1 := hn 2 (by norm_num) 3 (by norm_num) (by norm_num)
    have h2 := hn 2 (by norm_num) 4 (by norm_num) (by norm_num)
    have h3 := hn 2 (by norm_num) 5 (by norm_num) (by norm_num)
    have h4 := hn 2 (by norm_num) 6 (by norm_num) (by norm_num)
    have h5 := hn 2 (by norm_num) 7 (by norm_num) (by norm_num)
    have h6 := hn 2 (by norm_num) 8 (by norm_num) (by norm_num)
    have h7 := hn 2 (by norm_num) 9 (by norm_num) (by norm_num)
    have h8 := hn 2 (by norm_num) 10 (by norm_num) (by norm_num)
    have h9 := hn 3 (by norm_num) 4 (by norm_num) (by norm_num)
    have h10 := hn 3 (by norm_num) 5 (by norm_num) (by norm_num)
    have h11 := hn 3 (by norm_num) 6 (by norm_num) (by norm_num)
    have h12 := hn 3 (by norm_num) 7 (by norm_num) (by norm_num)
    have h13 := hn 3 (by norm_num) 8 (by norm_num) (by norm_num)
    have h14 := hn 3 (by norm_num) 9 (by norm_num) (by norm_num)
    have h15 := hn 3 (by norm_num) 10 (by norm_num) (by norm_num)
    have h16 := hn 4 (by norm_num) 5 (by norm_num) (by norm_num)
    have h17 := hn 4 (by norm_num) 6 (by norm_num) (by norm_num)
    have h18 := hn 4 (by norm_num) 7 (by norm_num) (by norm_num)
    have h19 := hn 4 (by norm_num) 8 (by norm_num) (by norm_num)
    have h20 := hn 4 (by norm_num) 9 (by norm_num) (by norm_num)
    have h21 := hn 4 (by norm_num) 10 (by norm_num) (by norm_num)
    have h22 := hn 5 (by norm_num) 6 (by norm_num) (by norm_num)
    have h23 := hn 5 (by norm_num) 7 (by norm_num) (by norm_num)
    have h24 := hn 5 (by norm_num) 8 (by norm_num) (by norm_num)
    have h25 := hn 5 (by norm_num) 9 (by norm_num) (by norm_num)
    have h26 := hn 5 (by norm_num) 10 (by norm_num) (by norm_num)
    have h27 := hn 6 (by norm_num) 7 (by norm_num) (by norm_num)
    have h28 := hn 6 (by norm_num) 8 (by norm_num) (by norm_num)
    have h29 := hn 6 (by norm_num) 9 (by norm_num) (by norm_num)
    have h30 := hn 6 (by norm_num) 10 (by norm_num) (by norm_num)
    have h31 := hn 7 (by norm_num) 8 (by norm_num) (by norm_num)
    have h32 := hn 7 (by norm_num) 9 (by norm_num) (by norm_num)
    have h33 := hn 7 (by norm_num) 10 (by norm_num) (by norm_num)
    have h34 := hn 8 (by norm_num) 9 (by norm_num) (by norm_num)
    have h35 := hn 8 (by norm_num) 10 (by norm_num) (by norm_num)
    have h36 := hn 9 (by norm_num) 10 (by norm_num) (by norm_num)
    interval_cases n <;> all_goals omega