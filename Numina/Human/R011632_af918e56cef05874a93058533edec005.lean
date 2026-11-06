import Mathlib

theorem number_theory_134332 : 
  ∃ (P : Set ℤ), ( ∀ x ∈ P, ∀ y ∈ P, x + y ∈ P) ∧ 
    (∃ x, x > 0 ∧ x ∈ P) ∧ ( ∃ x, x < 0 ∧ x ∈ P) ∧ (∃ x, Odd x ∧ x ∈ P) ∧ 
    (∃ x, Even x ∧ x ∈ P) ∧ ( -1 ∉ P) ∧
    ((0 ∈ P ∧ 2 ∉ P) ∧ ¬ (0 ∉ P ∧ 2 ∈ P) ∧ ¬(0 ∈ P ∧ 2 ∈ P) ∧ ¬(0 ∉ P ∧ 2 ∉ P) ):= by 
  let f : ℤ → ℤ := fun x => 3 * x
  let P : Set ℤ := Set.image f (Set.univ : Set ℤ)
  use P
  constructor
  -- goal 1 : ∀ x ∈ P, ∀ y ∈ P, x + y ∈ P
  intro x hx y hy
  -- discuss by_cases 
  unfold P at hx hy ⊢
  simp at hx hy ⊢
  obtain ⟨x1, hx1⟩ := hx
  obtain ⟨y1, hy1⟩ := hy
  unfold f at hx1 hy1
  use (x1 + y1)
  unfold f
  rw [←hx1, ←hy1]
  ring
  constructor
  -- goal 2 : ∃ x > 0, x ∈ P
  use 3
  constructor
  linarith
  unfold P
  unfold f
  simp
  constructor
  -- goal 3 : ∃ x < 0, x ∈ P
  use -3
  constructor
  linarith
  unfold P
  unfold f
  simp
  use (-1)
  ring
  constructor
  -- goal 5 : ∃ x odd, x ∈ P
  use 3
  constructor
  unfold Odd
  use 1
  norm_num
  unfold P
  unfold f
  simp
  constructor
  -- goal 6 : ∃ x even, x ∈ P
  use 0
  constructor
  unfold Even
  use 0
  norm_num
  unfold P
  unfold f
  simp
  constructor
  -- goal 7 : -1 ∉ P
  intro h
  unfold P at h
  simp at h
  obtain ⟨f1, hf1⟩ := h
  unfold f at hf1
  omega
  constructor
  -- goal 8 : (0 ∈ P ∧ 2 ∉ P)
  constructor
  unfold P
  unfold f
  simp
  intro h
  unfold P at h
  simp at h
  obtain ⟨f1, hf1⟩ := h
  unfold f at hf1
  omega
  constructor
  -- goal 9 : ¬ (0 ∉ P ∧ 2 ∈ P)
  intro h
  cases' h with h1 h2
  unfold P at h2
  simp at h2
  obtain ⟨f1, hf1⟩ := h2
  unfold f at hf1
  omega
  constructor
  -- goal 10 : ¬ (0 ∈ P ∧ 2 ∈ P)
  intro h
  cases' h with h1 h2
  unfold P at h2
  simp at h2
  obtain ⟨f1, hf1⟩ := h2
  unfold f at hf1
  omega
  -- goal 11 : ¬ (0 ∉ P ∧ 2 ∉ P)
  intro h
  cases' h with h1 h2
  unfold P at h1
  simp at h1
  obtain h3 := h1 0
  unfold f at h3
  omega