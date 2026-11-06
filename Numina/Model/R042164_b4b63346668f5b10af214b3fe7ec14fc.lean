import Mathlib

theorem number_theory_238765 (a : ℕ → ℕ) (h : ∀ m, ∃! n, (a n = m) ∧ (1 ≤ n)): 
 ∃ l m: ℕ, 1 < l ∧ l < m ∧ a 1 + a m = 2 * a l := by
  set s:= {n | a n > a 1 ∧ 1 ≤ n} with hs
  have g: ∃ n, a n > a 1 ∧ 1 ≤ n := by 
    specialize h (a 1 + 1)
    obtain ⟨n, hn⟩ := h
    simp at hn
    rcases hn with ⟨hn1, hn2⟩
    use n
    simp [hn1]
  have s_ne: s.Nonempty := by
    simp [s]
    simp [Set.Nonempty]
    simp [g]
  set l:= sInf s with hl
  have hl1:= Nat.sInf_mem s_ne
  rw [← hl] at hl1
  simp [s] at hl1
  rcases hl1 with ⟨hl2,bl⟩
  set x:= 2 * a l - a 1 with hx
  have hm:= h x
  obtain ⟨m, hm⟩ := hm
  simp at hm
  rcases hm with ⟨hm,o⟩
  clear o
  rcases hm with ⟨hm,bm⟩
  have ineq: a m > a 1 := by
    simp [hm,x]
    omega
  have m_in: m ∈ s := by
    simp [s]
    omega
  have l_lt_m: l ≤ m := by
    simp [l]
    apply Nat.sInf_le m_in
  replace l_lt_m: l < m := by
    by_contra! no
    replace no: l = m := by omega
    rw [← no] at hm
    simp [x] at hm
    omega
  have hl1' : l > 1 := by
    by_contra h'
    push_neg at h'
    have h1 : l ≤ 1 := by linarith
    have h2 : l = 0 ∨ l = 1 := by omega
    rcases h2 with (h2 | h2)
    · 
      simp [h2] at hl2 
      all_goals linarith
    · 
      simp [h2] at hl2 
      all_goals linarith
  use l, m
  constructor
  · exact hl1'
  constructor
  · exact l_lt_m
  · omega