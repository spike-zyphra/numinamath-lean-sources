import Mathlib

theorem number_theory_283744 : {x : ℕ × ℕ | x.1 * 2 + x.2 * 5 = 207}.encard = 21 := by
  have h1 : {x : ℕ × ℕ | x.1 * 2 + x.2 * 5 = 207} = Finset.filter (fun p : ℕ × ℕ => p.1 * 2 + p.2 * 5 = 207) (Finset.Icc (⟨0, 0⟩ : ℕ × ℕ) ⟨103, 41⟩) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try { native_decide }
  <;> try { aesop }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }
  <;> try { tauto }