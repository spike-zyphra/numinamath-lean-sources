import Mathlib

theorem number_theory_4019 : {(x, y) : ℕ × ℕ | 2 * x + 15 * y = 2020}.encard = 68 := by
  have h1 : {(x, y) : ℕ × ℕ | 2 * x + 15 * y = 2020} = Finset.filter (fun p : ℕ × ℕ => 2 * p.1 + 15 * p.2 = 2020) (Finset.Icc (0, 0) (1010, 134)) := by
    ext ⟨x, y⟩
    simp
    intro h
    omega
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try { native_decide }
  <;> try { 
    rw [Set.encard]
    simp [Set.ncard]
    <;> try { native_decide }
  }
  <;> try { 
    aesop
  }
  all_goals omega