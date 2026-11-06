import Mathlib

theorem number_theory_285748 {x y : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (hxy : x - y = 52) (h : (x ^ 2) % 100 = (y ^ 2) % 100) :
    x = 76 ∧ y = 24 := by 
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h1 : x = y + 52 := by 
    omega 
  rw [h1] at h
  interval_cases y <;> norm_num at h <;> try { 
    simp [h1]
    all_goals try { tauto }
    all_goals try { 
      omega 
    }
  } <;> omega 
  all_goals try { 
    omega 
  } <;> try { 
    ring_nf 
  }