import Mathlib

theorem algebra_304866 :
    {(p, q) : ℕ × ℕ | p ∈ Finset.Icc 2 5 ∧ q ∈ Finset.Icc 2 5 ∧ p ≠ q ∧
      ∃ x : ℝ, x > 2 ∧ p * x - 2 = x + q}.ncard = 6 := by
  have h1 : {(p, q) : ℕ × ℕ | p ∈ Finset.Icc 2 5 ∧ q ∈ Finset.Icc 2 5 ∧ p ≠ q ∧
      ∃ x : ℝ, x > 2 ∧ p * x - 2 = x + q} = {(2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)} := by
    ext ⟨p, q⟩
    simp [Finset.mem_Icc]
    constructor
    · -- First, prove that if (p, q) is in the left side set, it must be in the right side set
      rintro ⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩, hpq, ⟨x, hx1, hx2⟩⟩
      have h_eq : (p : ℝ) * x - 2 = (x : ℝ) + (q : ℝ) := by
        simpa using hx2
      have h7 : p ≤ 5 := by
        omega
      have h8 : q ≤ 5 := by
        omega
      have h9 : p ≥ 2 := by
        omega
      have h10 : q ≥ 2 := by
        omega
      interval_cases p <;> interval_cases q
      <;> norm_num at hpq h_eq hx1
      <;> norm_num at hpq h_eq hx1
      <;> try { 
        linarith 
      }
      <;> try { 
        exfalso 
        <;> nlinarith 
      }
      <;> norm_num
    · -- Now prove the reverse: if (p, q) is in the right side set, it's in the left side
      rintro (h | h | h | h | h | h)
      · -- (2, 3)
        rcases h with ⟨rfl, rfl⟩
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        · -- Show existence of x
          use 5
          norm_num
      · -- (2, 4)
        rcases h with ⟨rfl, rfl⟩
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        · -- Show existence of x
          use 6
          norm_num
      · -- (2, 5)
        rcases h with ⟨rfl, rfl⟩
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        · -- Show existence of x
          use 7
          norm_num
      · -- (3, 4)
        rcases h with ⟨rfl, rfl⟩
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        · -- Show existence of x
          use 3
          norm_num
      · -- (3, 5)
        rcases h with ⟨rfl, rfl⟩
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        · -- Show existence of x
          use (7 / 2 : ℝ)
          norm_num
      · -- (4, 5)
        rcases h with ⟨rfl, rfl⟩
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · decide
        · -- Show existence of x
          use (7 / 3 : ℝ)
          norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { 
    native_decide 
  }