import Mathlib

theorem number_theory_269094 :
    {(x, y) : ℕ × ℕ | x * 2 + y * 3 = 2016}.encard = 337 := by
  have h1 : {(x, y) : ℕ × ℕ | x * 2 + y * 3 = 2016} = Finset.filter (fun p => (p.1) * 2 + (p.2) * 3 = 2016) (Finset.Icc (0, 0) (1008, 672)) := by
    ext ⟨x, y⟩
    simp
    omega 
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try { native_decide }
  <;> try { tauto }