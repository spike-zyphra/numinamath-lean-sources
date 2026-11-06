import Mathlib

theorem number_theory_247266 (a b c : ℕ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : a ∈ Finset.Icc 0 9) (h' : b ∈ Finset.Icc 0 9) (h'' : c ∈ Finset.Icc 0 9)
    (h''' : 100 * a + 10 * b + c = Nat.factorial a + Nat.factorial b + Nat.factorial c) :
    a = 1 ∧ b = 4 ∧ c = 5 := by

  rw [Finset.mem_Icc] at h h' h''
  rcases h with ⟨ha0, ha9⟩
  rcases h' with ⟨hb0, hb9⟩
  rcases h'' with ⟨hc0, hc9⟩

  interval_cases a <;> interval_cases b <;> interval_cases c 
    <;> simp [Nat.factorial] at h'''
    <;> norm_num at h'''
    <;> try { 
      -- Verify that all digits are different
      try { tauto }
      <;> try { 
        exfalso
        try { omega }
      }
    }
    <;> norm_num
    <;> tauto