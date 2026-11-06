import Mathlib

theorem algebra_245088 (f : ℤ → ℤ) (hf : f = fun x => -x^2 + 20 * x - 64) :
    Set.ncard {p : ℤ × ℤ | p.1 > 0 ∧ p.2 > 0 ∧ f p.1 = p.2} = 11 := by 
  have h1 : {p : ℤ × ℤ | p.1 > 0 ∧ p.2 > 0 ∧ f p.1 = p.2} = 
    {(5, 11), (6, 20), (7, 27), (8, 32), (9, 35), (10, 36), (11, 35), (12, 32), (13, 27), (14, 20), (15, 11)} := by
    ext ⟨x, y⟩
    simp [hf]
    constructor
    · -- Assume ⟨x, y⟩ is in the left side.
      rintro ⟨hx1, hy1, heq⟩
      have h2 : x > 0 := hx1
      have h3 : y > 0 := hy1
      -- We have -x^2 + 20 * x - 64 = y
      have h4 : -x ^ 2 + 20 * x - 64 = y := by 
        linarith
      have h5 : x > 4 := by nlinarith
      have h6 : x < 16 := by nlinarith
      have hx2 : x ≤ 15 := by linarith
      interval_cases x <;> omega 
    · -- Assume ⟨x, y⟩ is in the right side.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (5, 11)
        constructor
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 5 = 11
          norm_num [hf]
      · -- (6, 20)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 6 = 20
          norm_num [hf]
      · -- (7, 27)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 7 = 27
          norm_num [hf]
      · -- (8, 32)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 8 = 32
          norm_num [hf]
      · -- (9, 35)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 9 = 35
          norm_num [hf]
      · -- (10, 36)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 10 = 36
          norm_num [hf]
      · -- (11, 35)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 11 = 35
          norm_num [hf]
      · -- (12, 32)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 12 = 32
          norm_num [hf]
      · -- (13, 27)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 13 = 27
          norm_num [hf]
      · -- (14, 20)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 14 = 20
          norm_num [hf]
      · -- (15, 11)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show that f 15 = 11
          norm_num [hf]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }