import Mathlib

theorem algebra_307725 (f : ℝ → ℝ) (hf : f = fun x => -x^2 + 6 * x - 27 / 4) :
    Set.ncard {p : ℤ × ℤ | p.1 ≥ 0 ∧ p.2 ≥ 0 ∧ f p.1 ≥ p.2} = 7 := by
  have h1 : {p : ℤ × ℤ | p.1 ≥ 0 ∧ p.2 ≥ 0 ∧ f p.1 ≥ p.2} = {(2, 0), (2, 1), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x, y) in the set, prove in the finite set
      rintro ⟨hx, hy, hxy⟩
      have h2 : (x : ℝ) ≥ (0 : ℝ) := by exact_mod_cast hx
      have h3 : (y : ℝ) ≥ (0 : ℝ) := by exact_mod_cast hy
      have h4 : f x = - (x : ℝ) ^ 2 + 6 * (x : ℝ) - (27 / 4 : ℝ) := by 
        rw [hf]
      have h5 : (- (x : ℝ) ^ 2 + 6 * (x : ℝ) - (27 / 4 : ℝ) ) ≥ (y : ℝ) := by 
        simpa [h4] using hxy 
      have h6 : (y : ℝ) ≤ - (x : ℝ) ^ 2 + 6 * (x : ℝ) - (27 / 4 : ℝ) := by linarith 
      have h7 : (4 * y : ℝ) ≤ -4 * (x : ℝ) ^ 2 + 24 * (x : ℝ) - 27 := by 
        have h8 : (y : ℝ) ≤ - (x : ℝ) ^ 2 + 6 * (x : ℝ) - (27 / 4 : ℝ) := by linarith 
        have h9 : (4 * y : ℝ) ≤ 4 * (- (x : ℝ) ^ 2 + 6 * (x : ℝ) - (27 / 4 : ℝ) ) := by 
          nlinarith 
        ring_nf at h9 ⊢ 
        linarith 
      have h8 : 4 * y ≤ -4 * x ^ 2 + 24 * x - 27 := by 
        exact_mod_cast h7 
      have h11 : x ≤ 4 := by nlinarith [sq_nonneg ((x : ℝ) - 4.5 : ℝ), sq_nonneg ((x : ℝ) - 1.5 : ℝ)]
      have h12 : x ≥ 2 := by nlinarith [sq_nonneg ((x : ℝ) - 4.5 : ℝ), sq_nonneg ((x : ℝ) - 1.5 : ℝ)]
      interval_cases x <;> omega 
    · -- Assume in the finite set, prove in the set
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (2, 0)
        constructor
        · norm_num 
        constructor
        · norm_num 
        · -- Show f 2 ≥ (0 : ℝ)
          rw [hf]
          norm_num 
      · -- (2, 1)
        constructor 
        · norm_num 
        constructor
        · norm_num 
        · -- Show f 2 ≥ (1 : ℝ)
          rw [hf]
          norm_num 
      · -- (3, 0)
        constructor
        · norm_num 
        constructor
        · norm_num 
        · -- Show f 3 ≥ (0 : ℝ)
          rw [hf]
          norm_num 
      · -- (3, 1)
        constructor 
        · norm_num 
        constructor
        · norm_num 
        · -- Show f 3 ≥ (1 : ℝ)
          rw [hf]
          norm_num 
      · -- (3, 2)
        constructor 
        · norm_num 
        constructor
        · norm_num 
        · -- Show f 3 ≥ (2 : ℝ)
          rw [hf]
          norm_num 
      · -- (4, 0)
        constructor 
        · norm_num 
        constructor
        · norm_num 
        · -- Show f 4 ≥ (0 : ℝ)
          rw [hf]
          norm_num 
      · -- (4, 1)
        constructor 
        · norm_num 
        constructor
        · norm_num 
        · -- Show f 4 ≥ (1 : ℝ)
          rw [hf]
          norm_num 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }