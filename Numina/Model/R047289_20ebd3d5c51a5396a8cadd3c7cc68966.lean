import Mathlib


theorem number_theory_70447 :
    IsLeast {n : ℕ | 0 < n ∧ ∀ i ∈ Finset.range 73, Nat.Coprime (i + 19) (n + i + 21)} 95 := by
  constructor
  · -- Show 95 is in the set
    constructor
    · norm_num
    · intro i hi
      rw [Finset.mem_range] at hi
      have h1 : i < 73 := by linarith
      interval_cases i <;> norm_num
  · -- Show 95 is the minimum element in the set
    intro n hn
    rcases hn with ⟨hn_pos, h⟩
    by_contra h1
    push_neg at h1
    -- We need to derive a contradiction from h for all n with 0 < n < 95
    have h0 := h 0 (by norm_num)
    have h1' := h 1 (by norm_num)
    have h2 := h 2 (by norm_num)
    have h3 := h 3 (by norm_num)
    have h4 := h 4 (by norm_num)
    have h5 := h 5 (by norm_num)
    have h6 := h 6 (by norm_num)
    have h7 := h 7 (by norm_num)
    have h8 := h 8 (by norm_num)
    have h9 := h 9 (by norm_num)
    have h10 := h 10 (by norm_num)
    have h11 := h 11 (by norm_num)
    have h12 := h 12 (by norm_num)
    have h13 := h 13 (by norm_num)
    have h14 := h 14 (by norm_num)
    have h15 := h 15 (by norm_num)
    have h16 := h 16 (by norm_num)
    have h17 := h 17 (by norm_num)
    have h18 := h 18 (by norm_num)
    have h19 := h 19 (by norm_num)
    have h20 := h 20 (by norm_num)
    have h21 := h 21 (by norm_num)
    have h22 := h 22 (by norm_num)
    have h23 := h 23 (by norm_num)
    have h24 := h 24 (by norm_num)
    have h25 := h 25 (by norm_num)
    have h26 := h 26 (by norm_num)
    have h27 := h 27 (by norm_num)
    have h28 := h 28 (by norm_num)
    have h29 := h 29 (by norm_num)
    have h30 := h 30 (by norm_num)
    have h31 := h 31 (by norm_num)
    have h32 := h 32 (by norm_num)
    have h33 := h 33 (by norm_num)
    have h34 := h 34 (by norm_num)
    have h35 := h 35 (by norm_num)
    have h36 := h 36 (by norm_num)
    have h37 := h 37 (by norm_num)
    have h38 := h 38 (by norm_num)
    have h39 := h 39 (by norm_num)
    have h40 := h 40 (by norm_num)
    have h41 := h 41 (by norm_num)
    have h42 := h 42 (by norm_num)
    have h43 := h 43 (by norm_num)
    have h44 := h 44 (by norm_num)
    have h45 := h 45 (by norm_num)
    have h46 := h 46 (by norm_num)
    have h47 := h 47 (by norm_num)
    have h48 := h 48 (by norm_num)
    have h49 := h 49 (by norm_num)
    have h50 := h 50 (by norm_num)
    have h51 := h 51 (by norm_num)
    have h52 := h 52 (by norm_num)
    have h53 := h 53 (by norm_num)
    have h54 := h 54 (by norm_num)
    have h55 := h 55 (by norm_num)
    have h56 := h 56 (by norm_num)
    have h57 := h 57 (by norm_num)
    have h58 := h 58 (by norm_num)
    have h59 := h 59 (by norm_num)
    have h60 := h 60 (by norm_num)
    have h61 := h 61 (by norm_num)
    have h62 := h 62 (by norm_num)
    have h63 := h 63 (by norm_num)
    have h64 := h 64 (by norm_num)
    have h65 := h 65 (by norm_num)
    have h66 := h 66 (by norm_num)
    have h67 := h 67 (by norm_num)
    have h68 := h 68 (by norm_num)
    have h69 := h 69 (by norm_num)
    have h70 := h 70 (by norm_num)
    have h71 := h 71 (by norm_num)
    have h72 := h 72 (by norm_num)
    interval_cases n <;> norm_num [Nat.Coprime] at h0 h1' h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 ⊢
    all_goals try { contradiction }